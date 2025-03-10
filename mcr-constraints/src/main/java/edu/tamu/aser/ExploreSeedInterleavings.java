package edu.tamu.aser;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.ObjectOutputStream;
import java.util.*;
import java.util.Map.Entry;
import java.util.stream.Collectors;

import edu.tamu.aser.config.Configuration;
import edu.tamu.aser.constraints.ConstraintsBuildEngine;
import edu.tamu.aser.trace.AbstractNode;
import edu.tamu.aser.trace.IMemNode;
import edu.tamu.aser.trace.LockNode;
import edu.tamu.aser.trace.ReadNode;
import edu.tamu.aser.trace.Trace;
import edu.tamu.aser.trace.UnlockNode;
import edu.tamu.aser.trace.WriteNode;

//import static edu.tamu.aser.scheduling.strategy.MCRStrategy.traces;
//import static edu.tamu.aser.scheduling.strategy.RVPORStrategy.toExplore;

/**
 * The MCRTest class implements maximal causal model based systematic
 * testing algorithm based on constraint solving.
 * The events in the trace are loaded and processed window
 * by window with a configurable window size.
 *
 * @author jeffhuang and shiyou huang
 *
 */
public class ExploreSeedInterleavings {
	private Queue<List<String>> schedules;

	private static int schedule_id;
	public static String output = "#Read, #Constraints, SolvingTime(ms)\n";
	public static HashSet<Object> races = new HashSet<Object>();
	private static boolean isfulltrace =false;
	private static ConstraintsBuildEngine iEngine;

	//prefix-setOfEquivalentPrefixes_map
	static HashMap<Vector<String>, Set<Vector<String>>> mapPrefixEquivalent = new HashMap<>();
	static long memUsed = 0;

	Set<Trace> traces;

	int period=-1;


	ExploreSeedInterleavings(Queue<List<String>> exploreQueue) {
		this.schedules = exploreQueue;
	}
	ExploreSeedInterleavings(Queue<List<String>> exploreQueue,Set<Trace> traces,int period) {
		this.schedules = exploreQueue;
		this.traces=traces;
		this.period=period;
	}


	/**
	 * Trim the schedule to show the last 100 only entries
	 *
	 */
	private static Vector<String> trim(Vector<String> schedule)
	{
		if(schedule.size()>100)
		{
			Vector<String> s = new Vector<>();
			s.add("...");
			for(int i=schedule.size()-100;i<schedule.size();i++)
				s.add(schedule.get(i));
			return s;
		}
		else
			return schedule;
	}

	/**
	 * The method for generating causally different schedules.
	 * Each schedule enforces a read to be matched with a write that writes
	 * a different value.
	 * @param engine : the engine is for building the constraints and call the solver to solve them
	 * @param trace  : trace collected from the current execution, which only contains the events which appear after the
	 *               prior prefix
	 * @param schedule_prefix : the prefix that leads to this execution
	 */
	private void genereteCausallyDifferentSchedules(ConstraintsBuildEngine engine, Trace trace, Vector<String> schedule_prefix)
	{
		//OMCR
		Vector<HashMap<String, Set<Vector<String>>>> vReadValuePrefixes =
				new Vector<>();
		/*
		 * for each shared variable, find all the reads and writes to this variable
		 * group the writes based on the value written to this variable
		 * consider each read to check if it can see a different value
		 */
		for (String addr : trace.getIndexedThreadReadWriteNodes().keySet()) {

			//the dynamic memory location
			//get the initial value on this address
			final String initVal = trace.getInitialWriteValueMap().get(addr);

			//get all read nodes on the address
			Vector<ReadNode> readnodes = trace.getIndexedReadNodes().get(addr);

			//get all write nodes on the address
			Vector<WriteNode> writenodes = trace.getIndexedWriteNodes().get(addr);

			//skip if there is no write events to the address
			if (writenodes == null || writenodes.size() < 1)
				continue;

			//check if local variable
			if (trace.isLocalAddress(addr))
				continue;

			HashMap<String, ArrayList<WriteNode>> valueMap = new HashMap<String, ArrayList<WriteNode>>();
			//group writes by their value
			for (WriteNode wnode : writenodes) {
				String v = wnode.getValue();
				ArrayList<WriteNode> list = valueMap.get(v);
				if (list == null) {
					list = new ArrayList<>();
					valueMap.put(v, list);
				}
				list.add(wnode);
			}

			//check read-write
			if (readnodes != null) {
				for (ReadNode readnode : readnodes) {

					HashMap<String, Set<Vector<String>>> mValuesPrefixes = new HashMap<>();
					//if isfulltrace, only consider the read nodes that happen after the prefix
					if (isfulltrace && readnode.getGID() <= schedule_prefix.size())
						continue;

					String rValue = readnode.getValue();
					//1. first check if the rnode can read from the initial value which is different from rValue
					boolean success = false;
					if (initVal == null && !rValue.equals("0")
							|| initVal != null && !initVal.equals(rValue)) {
						success = checkInitial(engine, trace, schedule_prefix, writenodes,
								readnode, initVal, mValuesPrefixes);
					}

					//2. then check if it can read from a particular write
					for (final String wValue : valueMap.keySet()) {
						if (!wValue.equals(rValue)) {
							//if it already reads from the initial value, then skip it
							if (wValue.equals(initVal) && success) {
								continue;
							}
							checkReadWrite(engine, trace, schedule_prefix, valueMap, readnode, wValue, mValuesPrefixes);
						}
					}
					//for each read, add the values and the corresponding prefixes to the vector
					if (!mValuesPrefixes.isEmpty()) {
						vReadValuePrefixes.add(mValuesPrefixes);
					}
				} //end for check read write
			}
		}  //end while

		memUsed += memSize(vReadValuePrefixes);

		if (Configuration.OMCR) {
			//local
			HashMap<Vector<String>, Set<Vector<String>>> localMapPrefixEquClass =
					new HashMap<>();
			//compute the equivalent prefixes
			computeEquPrefixes(vReadValuePrefixes,trace, localMapPrefixEquClass);
			memUsed += memSize(localMapPrefixEquClass);
			//
			Set<Vector<String>> equPrefixes = null;
			if (mapPrefixEquivalent.containsKey(schedule_prefix)) {
				equPrefixes = mapPrefixEquivalent.get(schedule_prefix);
			}
			//check each new prefix
			//for each read
			for (HashMap<String, Set<Vector<String>>> valuePrefixes : vReadValuePrefixes) {
				//for each value
				for (Set<Vector<String>> setPrefixes : valuePrefixes.values()) {
					//choose the prefix with max equivalent prefixes
					int num = 0;
					Iterator<Vector<String>> itPrefix = setPrefixes.iterator();
					Vector<String> prefix = null;

					//for each prefix that make the read return the value
					while (itPrefix.hasNext()) {
						Vector<String> tmp = itPrefix.next();
						Vector<String> prefix1 = new Vector<>();
						for (String xi : tmp) {
							long gid = Long.valueOf(xi.substring(1));
							long tid = trace.getNodeGIDTIdMap().get(gid);
							String name = trace.getThreadIdNameMap().get(tid);
							prefix1.add(name);
						}

						int flag = 0;
						if (equPrefixes != null) {
							//it may not in the same order
							for (Vector<String> p : equPrefixes) {
								Vector<String> copy = new Vector<>(p);
								Collections.sort(copy);
								Collections.sort(prefix1);
								if (copy.equals(prefix1)) {
//									System.err.println("test");
									flag = 1;
									break;
								}
							}
						}

						if (flag == 1) {
							continue;
						}

						if (localMapPrefixEquClass.containsKey(tmp)) {
							if (localMapPrefixEquClass.get(tmp).size() > num) {
								num = localMapPrefixEquClass.get(tmp).size();
								prefix = tmp;
							}
						} else if (prefix == null) {
							prefix = tmp;
						}
					}

					if (prefix != null) {
						omcrGenSchedule(trace, prefix, schedule_prefix, localMapPrefixEquClass);
					}
				}
			}
		}
	}


	private boolean checkInitial(ConstraintsBuildEngine engine, Trace trace,
								 Vector<String> schedule_prefix, Vector<WriteNode> writenodes,
								 ReadNode rnode, String initVal,
								 HashMap<String, Set<Vector<String>>> mValuesPrefixes) {
		//construct constraints and generate schedule
		HashSet<AbstractNode> depNodes = engine.getDependentNodes(trace,rnode);

		HashSet<AbstractNode> readDepNodes = new HashSet<AbstractNode>();
		//OMCR
		HashMap<String, Set<Vector<String>>> mValuePrefix = new HashMap<>();
		Set<Vector<String>> prefix = new HashSet<Vector<String>>();

		if(isfulltrace && schedule_prefix.size()>0)
			depNodes.addAll(trace.getFullTrace().subList(0, schedule_prefix.size()));


		depNodes.add(rnode);
		readDepNodes.add(rnode);

		StringBuilder sb;
		sb = engine.constructFeasibilityConstraints(trace,depNodes,readDepNodes, rnode, null);
		StringBuilder sb2;
		sb2 = engine.constructReadInitWriteConstraints(rnode,depNodes, writenodes);

		sb.append(sb2);
		//@alan
		//adding rnode.getGid() as a parameter
		Vector<String> schedule = engine.generateSchedule(sb,rnode.getGID(),rnode.getGID(),isfulltrace?schedule_prefix.size():0);

		output = output + Configuration.numReads + " " +
				Configuration.rwConstraints + " " +
				Configuration.solveTime + "\n";

		if(schedule!=null){
			if (Configuration.OMCR) {
				prefix.add(schedule);
				mValuesPrefixes.put(initVal, prefix);
//				vReadValuePrefixes.add(mValuePrefix);
				return true;
			}
			else{
				generateSchedule(schedule,trace,schedule_prefix,rnode.getID(),rnode.getValue(),initVal,-1);
				return true;
			}

		}
		return false;
	}

	/**
	 * check if a read can read from a particular write
	 */
	private void checkReadWrite(
			ConstraintsBuildEngine engine,
			Trace trace,
			Vector<String> schedule_prefix,
			HashMap<String, ArrayList<WriteNode>> valueMap,
			ReadNode rnode,
			String wValue,
			HashMap<String, Set<Vector<String>>> mValuesPrefixes)
	{
		Vector<AbstractNode> otherWriteNodes = new Vector<AbstractNode>();

		//OMCR

		Set<Vector<String>> prefix = new HashSet<Vector<String>>();

		for (Entry<String, ArrayList<WriteNode>> entry : valueMap.entrySet()) {
			if (!entry.getKey().equals(wValue))
				otherWriteNodes.addAll(entry.getValue());
		}

		ArrayList<WriteNode> wnodes = valueMap.get(wValue);
		Vector<Long> tids = new Vector<>();

		for (WriteNode wnode : wnodes) {
			if (tids.contains(wnode.getTid())) {
				continue;
			}
			if (rnode.getTid() != wnode.getTid()) {
				//check whether possible for read to match with write
				//can reach means a happens before relation
				//the first if-condition is a little strange
				if (rnode.getGID() > wnode.getGID() || !engine.canReach(rnode, wnode)) {

					//for all the events that happen before the target read and chosen write
					HashSet<AbstractNode> depNodes = new HashSet<>();

					//only for all the events that happen before the target read
					HashSet<AbstractNode> readDepNodes = new HashSet<>();

					if (isfulltrace && schedule_prefix.size() > 0)
						depNodes.addAll(trace.getFullTrace().subList(0, schedule_prefix.size()));

					//1. first find all the dependent nodes
					depNodes.add(rnode);
					depNodes.add(wnode);

					readDepNodes.add(rnode);

					/*
					 * After using static analysis, some reads can be removed
					 * but they cannot be removed, otherwise the order calculated will be wrong
					 * it just needs to ignore the feasibility constraints of these reads
					 * @author Alan
					 */
					HashSet<AbstractNode> nodes1 = engine.getDependentNodes(trace, rnode);
					HashSet<AbstractNode> nodes2 = engine.getDependentNodes(trace, wnode);

					depNodes.addAll(nodes1);
					depNodes.addAll(nodes2);

					readDepNodes.addAll(nodes1);

					//construct feasibility constraints
					StringBuilder sb =
							engine.constructFeasibilityConstraints(trace, depNodes, readDepNodes, rnode, wnode);

					//construct read write constraints, namely, all other writes either happen before the Write
					//or after the Read.
					StringBuilder sb3 =
							engine.constructReadWriteConstraints(depNodes, rnode, wnode, otherWriteNodes);

					sb.append(sb3);

					Vector<String> schedule =
							engine.generateSchedule(sb, rnode.getGID(), wnode.getGID(), isfulltrace ? schedule_prefix.size() : 0);

					//each time compute a causal schedule, record the information of #read, #constraints, time
					output = output + Long.toString(Configuration.numReads) + " " +
							Long.toString(Configuration.rwConstraints) + " " +
							Long.toString(Configuration.solveTime) + "\n";

					if (schedule != null) {
						if (Configuration.OMCR) {
							//TODO: compute the equivalent class of prefixes
							prefix.add(schedule);
							tids.add(wnode.getTid());

						} else {
							//rnode.getID or GID??
							generateSchedule(schedule, trace, schedule_prefix, rnode.getID(), rnode.getValue(), wValue, wnode.getID());
							break;
						}
					}
				}
			}
		}// end for_writes

		//add the equivalent class to the whole vector
		if (Configuration.OMCR && !prefix.isEmpty()) {
			mValuesPrefixes.put(wValue, prefix);
		}
	}


	/**
	 * Among the new prefix generated, check if any two of them could lead to redundant executions
	 */
	private void computeEquPrefixes(
			Vector<HashMap<String, Set<Vector<String>>>> schedules,
			Trace trace,
			HashMap<Vector<String>, Set<Vector<String>>> localMapPrefixEquClass)
	{
		//iterate over reads
		for (int i = 0; i < schedules.size() - 1; i++) {
			HashMap<String, Set<Vector<String>>> mVauePrefix = schedules.get(i);
			//iterate each value that this read can return
			for(Entry<String, Set<Vector<String>>> entryA : mVauePrefix.entrySet()){
				String vA = entryA.getKey();
				Set<Vector<String>> prefixes = entryA.getValue();
				//get prefix A
				for (Vector<String> pA : prefixes){
					//compare with prefix B
					for (int j = i+1; j < schedules.size(); j++){
						HashMap<String, Set<Vector<String>>> mVauePrefix2 = schedules.get(j);
						for(Entry<String, Set<Vector<String>>> entryB : mVauePrefix2.entrySet()){
							String vB = entryB.getKey();
							Set<Vector<String>> prefixes2 = entryB.getValue();
							for (Vector<String> pB : prefixes2){
								Vector<String> pAB = new Vector<>();
								if (checkEquivalence(trace, pAB, pA, vA, pB, vB)){
									//add the equivalent prefix to the class
//									addToEquivalentClass(trace, pA, pAB, localMapPrefixEquClass);
									if (localMapPrefixEquClass.containsKey(pA)) {
										localMapPrefixEquClass.get(pA).add(pAB);
									} else {
										Set<Vector<String>> equClass = new HashSet<Vector<String>>();
										equClass.add(pAB);
										localMapPrefixEquClass.put(pA, equClass);
									}

								}
							}
						}
					}
				}
			}
		}

	}

	private static boolean checkEquivalence(Trace trace, Vector<String> pAB,
											Vector<String> pA, String vA, Vector<String> pB, String vB) {
		Vector<String> pBA = new Vector<>();
		String rA = pA.lastElement();
		String rB = pB.lastElement();
		if (pA.contains(rB) || pB.contains(rA)) {
			return false;
		}

		return combineTwoPrefixes(trace, pAB, pA, pB, rB, vB) &&
				combineTwoPrefixes(trace, pBA, pB, pA, rA, vA);
	}

	private static boolean combineTwoPrefixes(Trace trace, Vector<String> pAB, Vector<String> pA, Vector<String> pB,
											  String rB, String vB){
//		for (int i = 0; i < pA.size(); i++) {
//			pAB.add(pA.get(i));
//		}

		//needs to consider about the synchronizations
		//e.g., A: lock-read_x
		//      B: lock-read_y
		//lock-r_x-lock-read_y is infeasible
		long gidrB = Long.valueOf(rB.substring(1));
		long tidrB = trace.getNodeGIDTIdMap().get(gidrB);

		Stack<AbstractNode> stLocks = new Stack<AbstractNode>();
		Vector<AbstractNode> aTrace = trace.getFullTrace();
		for (String aPA : pA) {
			long index = Long.valueOf(aPA.substring(1)) - 1;
			AbstractNode aNode = aTrace.get((int) index);
			if (aNode instanceof LockNode) {
				stLocks.push(aNode);
			} else if (aNode instanceof UnlockNode) {
				if (!stLocks.isEmpty()) {
					stLocks.pop();
				}
			}
		}

		//if stLock is not empty, it means that the unlocks do not appear in the prefix
		if (!stLocks.isEmpty()) {
			HashMap<String, LockNode> mAddrTid = new HashMap<>();
			while(!stLocks.isEmpty()){
				LockNode l = (LockNode) stLocks.pop();
				String addr = l.getAddr();
				mAddrTid.put(addr, l);
			}

			for (String aPB : pB) {
				long index = Long.valueOf(aPB.substring(1)) - 1;
				AbstractNode aNode = aTrace.get((int) index);
				if (aNode instanceof LockNode) {
					String addr = ((LockNode) aNode).getAddr();
					if (mAddrTid.containsKey(addr)) {
						LockNode l = mAddrTid.get(addr);
						Vector<AbstractNode> tidTrace = trace.getThreadNodesMap().get(l.getTid());
						int index1 = tidTrace.indexOf(l);
						if (index1 != -1) {
							for (int j = index1 + 1; j < tidTrace.size(); j++) {
								AbstractNode absNode = tidTrace.get(j);
								String choice = "x" + absNode.getGID();
								if (!pA.contains(choice)) {
									pAB.add(choice);
									if (absNode instanceof UnlockNode) {
										break;
									}
								}
							}
						}
					}
				}
			}
		}

		for (String aPB : pB) {
			if (!pA.contains(aPB)) {
				pAB.add(aPB);
			}
		}
		long gid = Long.valueOf(rB.substring(1));
//		Vector<AbstractNode> tAbstractNodes = trace.getFullTrace();
//		AbstractNode node1 = tAbstractNodes.get((int) gid);
		ReadNode rNodeB = (ReadNode) trace.getFullTrace().get((int) gid - 1);
		String addr = rNodeB.getAddr();
		for (int j = pAB.size() - 2; j >=0; j--){
			long _gid = Long.valueOf(pAB.get(j).substring(1));
			AbstractNode node = trace.getFullTrace().get((int) _gid - 1);
			if (node instanceof WriteNode) {
				if (((WriteNode) node).getAddr().equals(addr)) {
					//write to the same address
					return ((WriteNode) node).getValue().equals(vB);
				}
			}
		}
		int k;
		for (k = pA.size() - 2; k >=0; k--){
			long _gid = Long.valueOf(pA.get(k).substring(1));
			AbstractNode node = trace.getFullTrace().get((int) _gid -1 );
			if (node instanceof WriteNode) {
				if (((WriteNode) node).getAddr().equals(addr)) {
					//write to the same address
					return ((WriteNode) node).getValue().equals(vB);
				}
			}
		}

		return k < 0;

	}

	private void omcrGenSchedule(Trace trace, Vector<String> schedule,
								 Vector<String> schedule_prefix,
								 HashMap<Vector<String>, Set<Vector<String>>> localMapPrefixEquClass){

		Vector<String> schedule_a = new Vector<String>();
		int start_index = 0;
		for (int i=start_index; i<schedule.size(); i++)
		{
			String xi = schedule.get(i);
			long gid = Long.valueOf(xi.substring(1));
			long tid = trace.getNodeGIDTIdMap().get(gid);
			String name = trace.getThreadIdNameMap().get(tid);
			schedule_a.add(name);
		}

		//debugging
//		System.out.println("prefix: " + schedule_a);

		if(!isfulltrace) {
			//add the schedule prefix to the head of the new schedule to make it a complete schedule
			schedule_a.addAll(0, schedule_prefix);
		}
//		System.out.println("causal schedule: " + schedule_a);
		schedules.add(schedule_a);
		//update the map_prefix_equivalent
		if (localMapPrefixEquClass.containsKey(schedule)) {
			Set<Vector<String>> equPrefixes = localMapPrefixEquClass.get(schedule);
			Set<Vector<String>> valuePrefixes = new HashSet<>();
			for (Vector<String> p : equPrefixes){
				Vector<String> v = new Vector<>();
				for (String xi : p) {
					long gid = Long.valueOf(xi.substring(1));
					long tid = trace.getNodeGIDTIdMap().get(gid);
					String name = trace.getThreadIdNameMap().get(tid);
					v.add(name);
				}
				valuePrefixes.add(v);
			}
			mapPrefixEquivalent.put(schedule_a, valuePrefixes);
		}

	}

	/**
	 * Generate the causal schedule
	 */
	private void generateSchedule(
			Vector<String> schedule,
			Trace trace,
			Vector<String> schedule_prefix,
			int rGid,
			String rValue,
			String wValue,
			int wID)
	{
		{
			Vector<String> schedule_a = new Vector<String>();

			//get the first start event
			//note that in the first execution, there might be some events before the start event
			//but for the next execution, these events will not be executed

			//but for RV example, these events are executed for the next execution
			//for the implementation, just make all the assignments under main

			//@Alan
			int start_index = 0;
			for (int i=start_index; i<schedule.size(); i++)
			{
				String xi = schedule.get(i);
				long gid = Long.valueOf(xi.substring(1));
				long tid = trace.getNodeGIDTIdMap().get(gid);
				String name = trace.getThreadIdNameMap().get(tid);

				//add addr info to the schedule
				//the addr information is needed when replay yhe TSO/PSO schedule
				if (Objects.equals(Configuration.mode, "TSO") || Objects.equals(Configuration.mode, "PSO"))
				{
					String addr="";
					AbstractNode node = trace.getFullTrace().get((int) (gid-1));
					if(node instanceof ReadNode || node instanceof WriteNode){
						addr = ((IMemNode) node).getAddr();
						if(!Objects.equals(addr.split("\\.")[0], addr))
							addr = addr.split("\\.")[1];
					}
					if(Objects.equals(addr, "")){
						addr=""+node.getType();
					}
					name = name + "_" + addr;
				}

				schedule_a.add(name);
			}

			//debugging
//			System.out.println("prefix: " + schedule_a);

			if(!isfulltrace) {
				//add the schedule prefix to the head of the new schedule to make it a complete schedule
				schedule_a.addAll(0, schedule_prefix);
			}
//			else {
//				System.out.println(" USING FULL TRACE************");
//			}
//			System.out.println("causal schedule: " + schedule_a);
			schedules.add(schedule_a);

			if(Configuration.DEBUG)
			{
				//report the schedules
				String msg_header = "************* causal schedule "+(++schedule_id)+" **************\n";
				String msg_rwmeta = "Read-Write: "+trace.getStmtSigIdMap().get(rGid)+" -- "+(wID<0?"init":trace.getStmtSigIdMap().get(wID))+"\n";
				String msg_rwvalue = "Values: ("+rValue+"-"+wValue+")     ";
				String msg_schedule = "Schedule: "+trim(schedule_a)+"\n";
				String msg_footer = "**********************************************\n";

				report(msg_header+msg_rwmeta+msg_rwvalue+msg_schedule+msg_footer,MSGTYPE.STATISTICS);
			}
		}
	}

	private static void report(String msg, MSGTYPE type)
	{
		switch(type)
		{
			case REAL:
			case STATISTICS:
				System.err.println(msg);
				break;
			default: break;
		}
	}
	public enum MSGTYPE
	{
		REAL,POTENTIAL,STATISTICS
	}
	private static ConstraintsBuildEngine getEngine(String name)
	{
		if(iEngine==null){
			Configuration config = new Configuration();
			config.tableName = name;
			config.constraint_outdir = "tmp" + System.getProperty("file.separator") + "smt";

			iEngine = new ConstraintsBuildEngine(config);//EngineSMTLIB1
		}

		return iEngine;
	}

	/**
	 * start exploring the trace
	 * @param trace: the trace generated by re-execution
	 * @param schedule_prefix: prefix that leads to the generation of this trace
	 */
	void execute(Trace trace, Vector<String> schedule_prefix, Vector<AbstractNode> RawFullTrace,HashMap<Long, String> threadTidNameMap) {

		Configuration.numReads = 0;
		Configuration.rwConstraints = 0;
		Configuration.solveTime = 0;


		tidToTidNameMap=threadTidNameMap;
		//OPT: if #sv==0 or #shared rw ==0 continue
		if(trace.hasSharedVariable())
		{
			//engine is used for constructing constraints model
			//ConstraintsBuildEngine engine = getEngine(trace.getApplicationName());

			//pre-process the trace
			//build the initial happen before relation for some optimization
			//engine.preprocess(trace);

			//generate causal prefixes
			//genereteCausallyDifferentSchedules(engine,trace,schedule_prefix);
			generatePeriodicSchedules(
					new ArrayList<>(schedule_prefix),
					trace.getDkps(),
//					trace.getPeriod(),
					this.period,
					RawFullTrace// 使用实时传入的周期值

			);

		}
	}

	//compute the memory used
	static int memSize(Object o){
		try{
//            System.out.println("Index Size: " + ((ByteArrayOutputStream) o).size());
			ByteArrayOutputStream baos=new ByteArrayOutputStream();
			ObjectOutputStream oos=new ObjectOutputStream(baos);
			oos.writeObject(o);
			oos.close();
//            System.out.println("Data Size: " + baos.size() + "bytes.");
			return baos.size();
		}catch(IOException e){
			e.printStackTrace();
			return -1;
		}


	}
































	/* 论文核心算法实现
	 */
//
	// 新增成员变量，用于存储 label 到线程的映射关系
	private List<AbstractNode> dkpsNodes;

	// 假设类中已经有一个映射表，存储 tid 和 tidname 的对应关系
	private Map<Long, String> tidToTidNameMap;

	private void generatePeriodicSchedules(List<String> prefix, Map<String, Set<String>> dkps, int currentP, Vector<AbstractNode> rawFullTrace) {
		// 识别所有属于 dkps 的节点
		identifyDkpsNodes(dkps, rawFullTrace);

		// 使用 dkpsNodes 进行调度排序
		generateAllValidSchedules(prefix, currentP, rawFullTrace);
	}

	// 识别所有属于 dkps 的节点
	private void identifyDkpsNodes(Map<String, Set<String>> dkps, Vector<AbstractNode> rawFullTrace) {
		dkpsNodes = new ArrayList<>();
		for (AbstractNode node : rawFullTrace) {
			String tidName = tidToTidNameMap.get(node.getTid()); // 通过映射表获取 tidname
			String label = node.getLabel();
			if (tidName != null && dkps.containsKey(tidName) && dkps.get(tidName).contains(label)) {
				dkpsNodes.add(node);
			}
		}
	}

	private void generateAllValidSchedules(List<String> prefix, int p, Vector<AbstractNode> rawFullTrace) {
		// 1. 生成所有周期分配方案
		// 获取所有涉及的线程数
		Set<String> threadNames = new HashSet<>();
		for (AbstractNode node : dkpsNodes) {
			String tidName = tidToTidNameMap.get(node.getTid());
			if (tidName != null) {
				threadNames.add(tidName);
			}
		}
		int totalThreads = threadNames.size(); // 线程数
		List<Map<String, Integer>> allocs = generatePeriodAllocations(totalThreads, p);

		for (Map<String, Integer> alloc : allocs) { 
			// 2. 对每个线程生成所有分片组合
			Map<String, List<List<List<AbstractNode>>>> threadSplits = new HashMap<>();
			for (String tidName : threadNames) {
				int chunks = alloc.get(tidName); // 获取当前线程的分片数
				List<AbstractNode> nodes = getNodesByTidName(tidName);
				if (nodes != null) {
					threadSplits.put(tidName, generateAllSplits(nodes, chunks));
				}
			}

			// 3. 生成所有可能的交叉排列
			// 3. 初始化 selectedSplits 和 splitIndexMap
			Map<String, List<List<AbstractNode>>> selectedSplits = new HashMap<>();
			Map<String, Integer> splitIndexMap = new HashMap<>();

			// 4. 生成所有可能的交叉排列
			List<List<AbstractNode>> validSchedules = new ArrayList<>();

//			ListCombinations  combinations = new ListCombinations();
			List<List<List<List<AbstractNode>>>> combinations=ListCombinations.pickOneFromEach(threadSplits);

			for (List combination : combinations) {
				Set<List<AbstractNode>> combinationSet=extractLeafLists(combination);
				List<List<List<AbstractNode>>> res=SetPermutations.getPermutations(combinationSet);
				Iterator<List<List<AbstractNode>>> iterator = res.iterator();

				while (iterator.hasNext()) {
					List<List<AbstractNode>> schedule = iterator.next();
					if (!isValidSchedule(schedule)) {
						iterator.remove(); // 删除不合法的调度方案
					}
				}
//				validSchedules.forEach(schedule -> {
//					List<String> base = new ArrayList<>(prefix);
//					base.addAll(getTidNames(schedule));
//					List<String> full = inflateSchedule(schedule, rawFullTrace);
//					schedules.add(full);
//				});
				for (List<List<AbstractNode>> r:res) {
					List<AbstractNode> orders=new ArrayList<>();
					r.stream().forEach(list->list.forEach(orders::add));
					// 删除 orders 中出现在 prefix 里的节点
					List<AbstractNode> filteredOrders = new ArrayList<>();
					for (AbstractNode node : orders) {
						int index = rawFullTrace.indexOf(node); // 查找节点在 rawFullTrace 中的位置
						if (index >= prefix.size()) { // 只保留不在 prefix 范围内的节点
							filteredOrders.add(node);
						}
					}

					// 处理过滤后的 orders
					schedules.add(inflateSchedule(filteredOrders, rawFullTrace, prefix));
				}
			}



//			MapCombinationPicker picker=new MapCombinationPicker();

//			List<Map<String, List<List<AbstractNode>>>> combinations = picker.pickOneFromEach(threadSplits);







			// 5. 调用 backtrackCombine
//			backtrackCombine(threadSplits, selectedSplits, splitIndexMap, new ArrayList<>(), new ArrayList<>(), validSchedules);

			// 6. 添加到待探索队列

			// 4. 添加到待探索队列

		}
	}

	private static boolean isValidSchedule(List<List<AbstractNode>> schedule) {
		Long lastTid = null; // 记录上一个片段的线程 ID
		Map<Long, Long> lastGidMap = new HashMap<>(); // 记录每个线程的最后 GID

		for (List<AbstractNode> chunk : schedule) {
			if (chunk.isEmpty()) continue;

			Long currentTid = chunk.get(0).getTid(); // 当前片的线程 ID
			Long firstGid = chunk.get(0).getGid(); // 当前片第一个节点的 GID

			// 1. **检查线程交替**：相邻片不能属于同一个线程
			if (currentTid.equals(lastTid)) {
				return false; // 违反线程交替规则
			}
			lastTid = currentTid;

			// 2. **检查同一线程的 GID 递增**
			if (lastGidMap.containsKey(currentTid)) {
				if (firstGid <= lastGidMap.get(currentTid)) {
					return false; // 线程的 GID 必须递增
				}
			}

			// 3. 更新当前线程的最后 GID（取本片的最后一个 GID）
			lastGidMap.put(currentTid, chunk.get(chunk.size() - 1).getGid());
		}
		return true;
	}


	private  Set<List<AbstractNode>> extractLeafLists(List<List<List<AbstractNode>>> input) {
		Set<List<AbstractNode>> resultSet = new HashSet<>();
		if (input == null) return resultSet;
		for (List<List<AbstractNode>> middleList : input) {
			for (List<AbstractNode> leafList : middleList) {
				resultSet.add(leafList); // 直接添加最底层的 List<AbstractNode>
			}
		}
		return resultSet;
	}



	// 根据 tidname 获取属于该线程的所有节点
	private List<AbstractNode> getNodesByTidName(String tidName) {
		List<AbstractNode> nodes = new ArrayList<>();
		for (AbstractNode node : dkpsNodes) {
			String nodeTidName = tidToTidNameMap.get(node.getTid());
			if (nodeTidName != null && nodeTidName.equals(tidName)) {
				nodes.add(node);
			}
		}
		return nodes;
	}

	// 将节点列表转换为 tidname 列表
	private List<String> getTidNames(List<AbstractNode> nodes) {
		List<String> tidNames = new ArrayList<>();
		for (AbstractNode node : nodes) {
			tidNames.add(tidToTidNameMap.get(node.getTid()));
		}
		return tidNames;
	}

	private List<List<List<AbstractNode>>> generateAllSplits(List<AbstractNode> nodes, int chunks) {
		List<List<List<AbstractNode>>> result = new ArrayList<>();
		backtrackSplit(nodes, 0, chunks, new ArrayList<>(), result);
		return result;
	}

	private void backtrackSplit(List<AbstractNode> nodes, int index, int remainingChunks,
								List<List<AbstractNode>> current,
								List<List<List<AbstractNode>>> result) {
		// 如果已经分成了所有块，并且刚好用完所有节点，加入结果
		if (remainingChunks == 0) {
			if (index == nodes.size()) {
				result.add(new ArrayList<>(current));
			}
			return;
		}

		// 计算当前块的最大长度
		int maxSplitSize = nodes.size() - index - (remainingChunks - 1);

		// 从 1 到 maxSplitSize 依次尝试不同大小的子块
		for (int len = 1; len <= maxSplitSize; len++) {
			List<AbstractNode> split = new ArrayList<>(nodes.subList(index, index + len));
			current.add(split);
			backtrackSplit(nodes, index + len, remainingChunks - 1, current, result);
			current.remove(current.size() - 1); // 回溯撤销
		}
	}


	private List<Map<String, Integer>> generatePeriodAllocations(int totalThreads, int totalPeriods) {
		List<Map<String, Integer>> allocations = new ArrayList<>();
		if (totalThreads <= 0 || totalPeriods < totalThreads) {
			// 如果线程数或周期数不合法，直接返回空列表
			return allocations;
		}
		List<List<Integer>> res=BallDistribution.getAllDistributions(totalThreads,totalPeriods);
		for (List<Integer> threadPeriods : res){
			Map<String,Integer> threadPeriodsMap=new HashMap<>();
			for (int i = 0; i < threadPeriods.size(); i++) {
				threadPeriodsMap.put(String.valueOf(i),threadPeriods.get(i));
			}
			allocations.add(threadPeriodsMap);
		}
//		backtrackAllocate(totalThreads, totalPeriods - totalThreads,
//				new HashMap<>(), 0, allocations);
		return allocations;
	}

	private void backtrackAllocate(int remainingThreads, int remainingPeriods,
								   Map<String, Integer> currentAlloc,
								   int threadIndex,
								   List<Map<String, Integer>> result) {
		if (remainingThreads == 0) {
			if (remainingPeriods == 0) {
				// 找到一个有效的分配方案，添加到结果中
				result.add(new HashMap<>(currentAlloc));
			}
			return;
		}

		// 生成当前线程的 ID
		String threadId = String.valueOf(threadIndex ); // tidname 是单纯的数字

		// 计算当前线程可以分配的最大周期数
		int maxAlloc = remainingPeriods >= 0 ? 1 + remainingPeriods : 1;

		// 尝试为当前线程分配 1 到 maxAlloc 个周期
		for (int alloc = 1; alloc <= maxAlloc; alloc++) {
			currentAlloc.put(threadId, alloc);
			// 递归处理下一个线程，并更新剩余线程数和剩余周期数
			backtrackAllocate(remainingThreads - 1, remainingPeriods - (alloc - 1),
					currentAlloc, threadIndex + 1, result);
			// 回溯：移除当前线程的分配值
			currentAlloc.remove(threadId);
		}
	}

	// 填充调度顺序，保留非 dkps 的节点
	private List<String> inflateSchedule(List<AbstractNode> schedule, Vector<AbstractNode> rawFullTrace, List<String> prefix) {
		// 1. 记录每个线程需要删除的事件数
		Map<String, Integer> prefixCount = new HashMap<>();
		for (String tidName : prefix) {
			prefixCount.put(tidName, prefixCount.getOrDefault(tidName, 0) + 1);
		}

		// 2. 记录每个线程已经删除的事件数
		Map<String, Integer> removedTidCount = new HashMap<>();
		List<AbstractNode> filteredRawFullTrace = new ArrayList<>();

		// 3. 遍历 rawFullTrace，删除每个线程的前缀事件
		for (AbstractNode node : rawFullTrace) {
			String tidName = tidToTidNameMap.get(node.getTid());

			// 如果该线程在 prefix 中，并且还没有删除它需要删除的事件数量
			if (prefixCount.containsKey(tidName) && removedTidCount.getOrDefault(tidName, 0) < prefixCount.get(tidName)) {
				// 删除该线程的第一个事件
				removedTidCount.put(tidName, removedTidCount.getOrDefault(tidName, 0) + 1);
				continue;  // 跳过该线程的第一个事件
			}

			// 保留其他事件
			filteredRawFullTrace.add(node);
		}

		// 4. 记录每个线程已处理到的位置
		Map<String, Integer> pointers = new HashMap<>();
		for (AbstractNode node : filteredRawFullTrace) {
			String tidName = tidToTidNameMap.get(node.getTid());
			pointers.putIfAbsent(tidName, 0);  // 初始化指针
		}

		List<String> fullSchedule = new ArrayList<>();
		fullSchedule.addAll(prefix);

		int scheduleIndex = 0;  // 用来遍历 schedule

//		// 5. 处理剩余的 filteredRawFullTrace 中的节点
//		for (int i = 0; i < filteredRawFullTrace.size(); i++) {
//			AbstractNode node = filteredRawFullTrace.get(i);
//			String tidName = tidToTidNameMap.get(node.getTid());
//
//			// 如果当前节点是 schedule 中的关键节点
//			if (scheduleIndex < schedule.size() && node.equals(schedule.get(scheduleIndex))) {
//				// 填充 schedule 中的关键节点
//				fullSchedule.add(tidName);
//				scheduleIndex++;
//
//				// 更新当前线程的指针位置
//				pointers.put(tidName, i + 1);
//			} else {
//				// 如果不是关键节点，且当前线程已经处理到这个节点，则填充
//				int currentPtr = pointers.get(tidName);
//				if (i >= currentPtr) {
//					fullSchedule.add(tidName);
//					pointers.put(tidName, i + 1);
//				}
//			}
//		}

		for (int i=0;i<schedule.size();i++){
			int index=filteredRawFullTrace.indexOf(schedule.get(i));
			if (!pointers.containsKey(tidToTidNameMap.get(schedule.get(i).getTid()))){
				System.out.println("error");

			}
			int begin=pointers.get(tidToTidNameMap.get(schedule.get(i).getTid()));
			for (int j =begin;j<=index;j++){
				if (filteredRawFullTrace.get(j).getTid()==schedule.get(i).getTid()){
					fullSchedule.add(tidToTidNameMap.get(filteredRawFullTrace.get(j).getTid()));
				}
			}
			pointers.put(tidToTidNameMap.get(schedule.get(i).getTid()),index+1);
		}

		return fullSchedule;
	}






	// 在 rawFullTrace 中查找节点的位置
	private int findNodeIndex(Vector<AbstractNode> rawFullTrace, AbstractNode node, int start) {
		for (int i = start; i < rawFullTrace.size(); i++) {
			if (rawFullTrace.get(i).equals(node)) {
				return i;
			}
		}
		return -1;
	}


	private void backtrackCombine(Map<String, List<List<List<AbstractNode>>>> threadSplits,
								  Map<String, List<List<AbstractNode>>> selectedSplits,
								  Map<String, Integer> splitIndexMap,
								  List<AbstractNode> current, // 修复：current 类型改为 List<AbstractNode>
								  List<String> threadOrder,
								  List<List<AbstractNode>> result) {
		// 终止条件：所有分片选完
		int totalSplits = threadSplits.values().stream()
				.flatMap(List::stream)
				.mapToInt(List::size)
				.sum();
		if (current.size() == totalSplits) { // 修正：直接比较节点总数
			result.add(new ArrayList<>(current));
			return;
		}

		// 遍历所有线程
		for (String tidName : threadSplits.keySet()) {
			// 剪枝：防止相邻片来自同一个线程
			if (!threadOrder.isEmpty() && threadOrder.get(threadOrder.size() - 1).equals(tidName)) {
				continue;
			}

			// 获取该线程的所有分片组合（即可能的 splitCombination）
			List<List<List<AbstractNode>>> possibleSplits = threadSplits.get(tidName);
			if (possibleSplits.isEmpty()) continue;

			// 确保每个线程使用固定的 splitCombination
			List<List<AbstractNode>> chosenSplitCombination = selectedSplits.get(tidName);
			if (chosenSplitCombination == null) {
				chosenSplitCombination = possibleSplits.get(0);
//				possibleSplits.remove(0);
				selectedSplits.put(tidName, chosenSplitCombination);
				splitIndexMap.put(tidName, 0);
			}

			// 获取当前线程在 chosenSplitCombination 中的下一个分片索引
			int splitIndex = splitIndexMap.get(tidName);
			if (splitIndex >= chosenSplitCombination.size()) continue;

			// 选择下一个分片
			List<AbstractNode> nextSplit = chosenSplitCombination.get(splitIndex);
			List<AbstractNode> newCurrent = new ArrayList<>(current); // 修复：newCurrent 类型改为 List<AbstractNode>
			newCurrent.addAll(nextSplit); // 将分片中的节点全部加入调度序列

			// 更新 splitIndexMap
			Map<String, Integer> newSplitIndexMap = new HashMap<>(splitIndexMap);
			newSplitIndexMap.put(tidName, splitIndex + 1);

			// 更新线程顺序
			List<String> newThreadOrder = new ArrayList<>(threadOrder);
			newThreadOrder.add(tidName);

			// 递归调用
			backtrackCombine(threadSplits, selectedSplits, newSplitIndexMap, newCurrent, newThreadOrder, result);
		}
	}

//
//	private void generatePeriodicSchedules(List<String> prefix, Map<String, Set<String>> dkps, int currentP, Map<String, List<String>> rawFullTrace) {
//		// 生成新的 dkpsMap
//		Map<String, List<String>> dkpsMap = generateDkpsMap(dkps, rawFullTrace);
//
//		// 使用新的 dkpsMap 代替原来的 dkps
//		generateAllValidSchedules(prefix, dkpsMap, currentP, rawFullTrace);
//	}
//
//	private Map<String, List<String>> generateDkpsMap(Map<String, Set<String>> dkps, Map<String, List<String>> rawFullTrace) {
//		Map<String, List<String>> dkpsMap = new HashMap<>();
//
//		// 遍历 rawFullTrace
//		for (Map.Entry<String, List<String>> entry : rawFullTrace.entrySet()) {
//			String tidName = entry.getKey();
//			List<String> events = entry.getValue();
//			List<String> dkpEvents = new ArrayList<>();
//
//			// 遍历每个线程的事件
//			for (String event : events) {
//				// 如果事件在 dkps 中，则添加到 dkpEvents
//				if (dkps.containsKey(tidName) && dkps.get(tidName).contains(event)) {
//					dkpEvents.add(event);
//				}
//			}
//
//			// 如果该线程有 dkp 事件，则添加到 dkpsMap
//			if (!dkpEvents.isEmpty()) {
//				dkpsMap.put(tidName, dkpEvents);
//			}
//		}
//
//		return dkpsMap;
//	}
//
//	private void generateAllValidSchedules(List<String> prefix,
//										   Map<String, List<String>> threadGroups,
//										   int p, Map<String, List<String>> rawFullTrace) {
//		// 1. 生成所有周期分配方案
//		List<Map<String, Integer>> allocs = generatePeriodAllocations(threadGroups.size(), p);
//
//		for (Map<String, Integer> alloc : allocs) {
//			// 2. 对每个线程生成所有分片组合
//			Map<String, List<List<List<String>>>> threadSplits = new HashMap<>();
//			alloc.forEach((tidName, chunks) -> {
//				List<String> labels = threadGroups.get(tidName);
//				if (labels != null) {
//					// 直接使用 List<String> 而不是 Set<String>
//					threadSplits.put(tidName, generateAllSplits(labels, chunks));
//				}
//			});
//
//			// 3. 生成所有可能的交叉排列
//			List<List<String>> validSchedules = new ArrayList<>();
//			backtrackCombine(threadSplits, new LinkedList<>(), validSchedules);
//
//			// 4. 添加到待探索队列
//			validSchedules.forEach(schedule -> {
//				List<String> base = new ArrayList<>(prefix);
//				base.addAll(schedule);
//				List<String> full = inflateSchedule(base, rawFullTrace);
//				schedules.add(full);
//			});
//		}
//	}
//
//	private List<List<List<String>>> generateAllSplits(List<String> labels, int chunks) {
//		List<List<List<String>>> result = new ArrayList<>();
//		backtrackSplit(labels, chunks, 0, new ArrayList<>(), result);
//		return result;
//	}
//
//	private void backtrackSplit(List<String> remainingEvents, int remainingChunks,
//								int start, List<List<String>> current,
//								List<List<List<String>>> result) {
//		if (remainingChunks == 0) {
//			if (remainingEvents.isEmpty()) {
//				result.add(new ArrayList<>(current));
//			}
//			return;
//		}
//
//		if (remainingEvents.size() < remainingChunks) return;
//
//		int maxSplitSize = remainingEvents.size() - remainingChunks + 1;
//		for (int len = 1; len <= maxSplitSize; len++) {
//			List<String> split = new ArrayList<>(remainingEvents.subList(0, len));
//			current.add(split);
//			backtrackSplit(remainingEvents.subList(len, remainingEvents.size()),
//					remainingChunks - 1, 0, current, result);
//			current.remove(current.size() - 1);
//		}
//	}
//
//private List<Map<String, Integer>> generatePeriodAllocations(int totalThreads, int totalPeriods) {
//	List<Map<String, Integer>> allocations = new ArrayList<>();
//	if (totalThreads <= 0 || totalPeriods < totalThreads) {
//		// 如果线程数或周期数不合法，直接返回空列表
//		return allocations;
//	}
//	backtrackAllocate(totalThreads, totalPeriods - totalThreads,
//			new HashMap<>(), 0, allocations);
//	return allocations;
//}
//
//	private void backtrackAllocate(int remainingThreads, int remainingPeriods,
//								   Map<String, Integer> currentAlloc,
//								   int threadIndex,
//								   List<Map<String, Integer>> result) {
//		if (remainingThreads == 0) {
//			if (remainingPeriods == 0) {
//				// 找到一个有效的分配方案，添加到结果中
//				result.add(new HashMap<>(currentAlloc));
//			}
//			return;
//		}
//
//		// 生成当前线程的 ID
//		String threadId = "T" + (threadIndex + 1);
//
//		// 计算当前线程可以分配的最大周期数
//		int maxAlloc = remainingPeriods >= 0 ? 1 + remainingPeriods : 1;
//
//		// 尝试为当前线程分配 1 到 maxAlloc 个周期
//		for (int alloc = 1; alloc <= maxAlloc; alloc++) {
//			currentAlloc.put(threadId, alloc);
//			// 递归处理下一个线程，并更新剩余线程数和剩余周期数
//			backtrackAllocate(remainingThreads - 1, remainingPeriods - (alloc - 1),
//					currentAlloc, threadIndex + 1, result);
//			// 回溯：移除当前线程的分配值
//			currentAlloc.remove(threadId);
//		}
//	}
//
//	private List<String> inflateSchedule(List<String> baseSchedule,
//										 Map<String, List<String>> rawFullTrace) {
//		// 记录每个线程已处理到的位置
//		Map<String, Integer> pointers = new HashMap<>();
//		rawFullTrace.forEach((tidName, events) -> pointers.put(tidName, 0));
//
//		List<String> fullSchedule = new ArrayList<>();
//
//		// 处理基础调度中的每个 label
//		for (String label : baseSchedule) {
//			String tidName = getThreadFromLabel(label); // 从 label 中提取 tidName
//			List<String> threadEvents = rawFullTrace.get(tidName);
//			if (threadEvents == null) continue;
//
//			// 找到该 label 在完整事件中的位置
//			int labelIndex = threadEvents.indexOf(label);
//			if (labelIndex == -1) continue;
//
//			// 添加从当前指针到 label 位置的所有事件
//			int currentPtr = pointers.get(tidName);
//			fullSchedule.addAll(threadEvents.subList(currentPtr, labelIndex + 1));
//
//			// 更新指针
//			pointers.put(tidName, labelIndex + 1);
//		}
//
//		// 添加各线程剩余事件
//		rawFullTrace.forEach((tidName, events) -> {
//			int ptr = pointers.get(tidName);
//			if (ptr < events.size()) {
//				fullSchedule.addAll(events.subList(ptr, events.size()));
//			}
//		});
//
//		return fullSchedule;
//	}
//
//	private void backtrackCombine(Map<String, List<List<List<String>>>> threadSplits,
//								  List<String> current,
//								  List<List<String>> result) {
//		// 终止条件：所有线程的分片用完
//		boolean allEmpty = threadSplits.values().stream()
//				.allMatch(splits -> splits.isEmpty());
//		if (allEmpty) {
//			result.add(new ArrayList<>(current));
//			return;
//		}
//
//		// 遍历所有线程
//		for (String tidName : threadSplits.keySet()) {
//			// 获取该线程的所有分片组合（三级嵌套）
//			List<List<List<String>>> splits = threadSplits.get(tidName);
//			if (splits.isEmpty()) continue;
//
//			// 剪枝：连续同线程检查
//			if (!current.isEmpty()) {
//				String lastTidName = getThreadFromLabel(current.get(current.size() - 1));
//				if (tidName.equals(lastTidName)) continue;
//			}
//
//			// 深拷贝当前线程的分片组合
//			List<List<List<String>>> remainingSplits = new ArrayList<>(splits);
//
//			// 遍历每个分片组合
//			for (List<List<String>> splitCombination : remainingSplits) {
//				// 生成新线程分片上下文
//				Map<String, List<List<List<String>>>> newThreadSplits = new HashMap<>(threadSplits);
//				newThreadSplits.put(tidName, Collections.singletonList(splitCombination));
//
//				// 遍历分片组合中的每个分片
//				for (List<String> nextSplit : splitCombination) {
//					List<String> newCurrent = new ArrayList<>(current);
//					newCurrent.addAll(nextSplit);
//					backtrackCombine(newThreadSplits, newCurrent, result);
//				}
//			}
//		}
//	}
//
//	private String getThreadFromLabel(String label) {
//		// 假设 label 的格式为 EventType_Address_TID，其中 TID 是线程的唯一标识符
//		String[] parts = label.split("_");
//		return parts[2]; // 提取 TID
//	}
//


}




  class ListCombinations {
	public static <K, T> List<List<T>> pickOneFromEach(Map<K, List<T>> inputMap) {
		List<List<T>> result = new ArrayList<>();
		if (inputMap == null || inputMap.isEmpty()) return result;

		List<K> keys = new ArrayList<>(inputMap.keySet()); // 获取所有 key
		backtrack(inputMap, keys, 0, new ArrayList<>(), result);
		return result;
	}

	private static <K, T> void backtrack(Map<K, List<T>> inputMap, List<K> keys, int depth,
										 List<T> current, List<List<T>> result) {
		if (depth == keys.size()) {
			result.add(new ArrayList<>(current));  // 组合完成，加入结果集
			return;
		}

		K currentKey = keys.get(depth);
		for (T item : inputMap.get(currentKey)) {
			current.add(item);  // 选取当前 key 的一个元素
			backtrack(inputMap, keys, depth + 1, current, result); // 递归进入下一层
			current.remove(current.size() - 1);  // 回溯，尝试其他选择
		}
	}

	public static void main(String[] args) {
		Map<String, List<String>> input = new HashMap<>();
		input.put("group1", Arrays.asList("A", "B"));
		input.put("group2", Arrays.asList("C", "D"));
		input.put("group3", Arrays.asList("E", "F"));

		List<List<String>> combinations = pickOneFromEach(input);
		for (List<String> combo : combinations) {
			System.out.println(combo);
		}
	}
}



 class SetPermutations {
	public static <T> List<List<T>> getPermutations(Set<T> inputSet) {
		List<T> inputList = new ArrayList<>(inputSet); // 将 Set 转换为 List
		List<List<T>> result = new ArrayList<>();
		boolean[] used = new boolean[inputList.size()];
		backtrack(inputList, new ArrayList<>(), used, result);
		return result;
	}

	private static <T> void backtrack(List<T> inputList, List<T> current, boolean[] used, List<List<T>> result) {
		if (current.size() == inputList.size()) {
			result.add(new ArrayList<>(current)); // 记录当前排列
			return;
		}

		for (int i = 0; i < inputList.size(); i++) {
			if (used[i]) continue; // 跳过已使用的元素

			used[i] = true;
			current.add(inputList.get(i));
			backtrack(inputList, current, used, result);
			current.remove(current.size() - 1); // 回溯
			used[i] = false;
		}
	}

	public static void main(String[] args) {
		Set<Integer> inputSet = new HashSet<>(Arrays.asList(1, 2, 3));
		List<List<Integer>> permutations = getPermutations(inputSet);
		for (List<Integer> perm : permutations) {
			System.out.println(perm);
		}
	}
}



class BallDistribution {

	public static void main(String[] args) {
		int n = 3; // Number of bins
		int m = 5; // Total number of balls, m >= n
		List<List<Integer>> distributions = getAllDistributions(n, m);

		// Print all possible distributions
		for (List<Integer> distribution : distributions) {
			System.out.println(distribution);
		}
	}

	/**
	 * Returns all distributions of m balls into n bins with each bin receiving at least one ball.
	 */
	public static List<List<Integer>> getAllDistributions(int n, int m) {
		List<List<Integer>> results = new ArrayList<>();
		// Allocate one ball per bin first, so we need to distribute (m - n) extra balls
		distribute(n, m - n, new ArrayList<>(), results);

		// Adjust each solution by adding 1 to each bin count
		List<List<Integer>> finalResults = new ArrayList<>();
		for (List<Integer> distribution : results) {
			List<Integer> finalDistribution = new ArrayList<>();
			for (int extra : distribution) {
				finalDistribution.add(extra + 1);
			}
			finalResults.add(finalDistribution);
		}
		return finalResults;
	}

	/**
	 * Recursive helper method to distribute remaining balls among bins.
	 *
	 * @param n         Total number of bins.
	 * @param remaining The number of extra balls to distribute.
	 * @param current   The current distribution (each value is the number of extra balls for a bin).
	 * @param results   The list of valid distributions.
	 */
	private static void distribute(int n, int remaining, List<Integer> current, List<List<Integer>> results) {
		// Base case: if we've assigned a value to all bins...
		if (current.size() == n) {
			// ...and there are no extra balls left, record the solution.
			if (remaining == 0) {
				results.add(new ArrayList<>(current));
			}
			return;
		}

		// For the current bin, try all possible extra ball counts from 0 to remaining.
		for (int i = 0; i <= remaining; i++) {
			current.add(i);
			distribute(n, remaining - i, current, results);
			current.remove(current.size() - 1);  // Backtrack.
		}
	}
}
