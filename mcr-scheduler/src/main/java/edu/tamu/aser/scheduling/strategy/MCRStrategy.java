package edu.tamu.aser.scheduling.strategy;

import java.util.*;
import java.util.Map.Entry;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.stream.Collectors;

import edu.tamu.aser.StartExploring;
import edu.tamu.aser.config.Configuration;
import edu.tamu.aser.instrumentation.RVGlobalStateForInstrumentation;
import edu.tamu.aser.trace.*;
import edu.tamu.aser.runtime.RVRunTime;
import edu.tamu.aser.scheduling.events.EventType;

public class MCRStrategy extends SchedulingStrategy {

	private Queue<List<String>> toExplore;
	public static List<Integer> choicesMade;
	public static List<String> schedulePrefix = new ArrayList<String>();
	private static Trace currentTrace;
	private boolean notYetExecutedFirstSchedule;
	private final static int NUM_THREADS = 10;
	private volatile static ExecutorService executor;
	private ThreadInfo previousThreadInfo;
	public static final Boolean fullTrace = false;  //default

	public static Set<Trace> traces=new HashSet<>();//Trace 加上prefix信息以及dkps信息
	//public static int p=2;
	public static int p = Configuration.getInitialConcurrency();

	private int count;
	public MCRStrategy() {
		count = 0;
	}


	/**
	 * before the execution
	 */
	@Override
	public void startingExploration() {
		this.toExplore = new ConcurrentLinkedQueue<List<String>>();
		this.notYetExecutedFirstSchedule = true;
		MCRStrategy.choicesMade = new ArrayList<Integer>();
		MCRStrategy.schedulePrefix = new ArrayList<String>();

		RVRunTime.currentIndex = 0;
		executor = Executors.newFixedThreadPool(NUM_THREADS);

	}

	/**
	 * called before a new schedule starts
	 */
	@Override
	public void startingScheduleExecution() {
		List<String> prefix = this.toExplore.poll();
		if (!MCRStrategy.choicesMade.isEmpty()) {   // when not empty
			MCRStrategy.choicesMade.clear();
			MCRStrategy.schedulePrefix = new ArrayList<String>();
			assert prefix != null;
			MCRStrategy.schedulePrefix.addAll(prefix);
//			for (String choice : prefix) {
//				MCRStrategy.schedulePrefix.add(choice);
//			}
		}

		RVRunTime.currentIndex = 0;
		RVRunTime.failure_trace.clear();
		initTrace();

		previousThreadInfo = null;
	}

	public static Trace getTrace() {
		return currentTrace;
	}

	/* problem here
	 * in the first execution, the initialized trace will be used by the aser-engine project
	 * however, in the first initialization, the trace hasn't been complete yet.
	 */
	private void initTrace() {
		RVRunTime.init();
		TraceInfo traceInfo = new TraceInfo(
				RVGlobalStateForInstrumentation.variableIdSigMap,
				new HashMap<Integer, String>(),
				RVGlobalStateForInstrumentation.stmtIdSigMap,
				RVRunTime.threadTidNameMap);
		traceInfo.setVolatileAddresses(RVGlobalStateForInstrumentation.instance.volatilevariables);
		currentTrace = new Trace(traceInfo);
	}





//	private Set<String> getDkps(Trace trace) { //该方法不适合在此地
//		Set<String> dkps = new HashSet<>();
//
//		// Iterate over all events in the trace and add key points (memory accesses and sync operations)
//		for (IMemNode node : trace.getAllMemoryNodes()) {
//			if (node instanceof ReadNode || node instanceof WriteNode) {
//				//String address = node.getAddr();
//				dkps.add(String.valueOf(node.getTid())); // Add memory access events to dkps
//				dkps.add(((AbstractNode) node).getLabel()); // Add memory access events to dkps
//
//			}
//		}
//
//		// Add synchronization events (locks and unlocks)
////		for (ISyncNode node : trace.getSyncNodes()) {
////			if (node instanceof LockNode || node instanceof UnlockNode) {
////				String address = node.getAddr();
////				dkps.add("SyncEvent_" + address + "_" + node.getTid()); // Add synchronization events to dkps
////			}
////		}
//
//		return dkps;
//	}


private Map<String, Set<String>> getDkps(Trace trace) {
	// 使用线程ID作为键，每个线程对应一个标签集合
	Map<String, Set<String>> dkps = new HashMap<>();

	for (IMemNode node : trace.getAllMemoryNodes()) {
		if (node instanceof ReadNode || node instanceof WriteNode) {
			String tid = String.valueOf(node.getTid());
			String label = ((AbstractNode) node).getLabel();

			// 初始化线程的标签集合（如果不存在）
			dkps.putIfAbsent(tid, new HashSet<>());

			// 将标签添加到对应线程的集合中
			dkps.get(tid).add(label);
		}
	}
	return dkps;
}

	// 在MCRStrategy类中添加方法
	private Map<String, Set<String>> findNewDKPs(Trace currentTrace) {
		// 1. 获取当前Trace的DKPs结构：Map<线程, Set<DKP>>
		Map<String, Set<String>> currentDKPs = currentTrace.getDkps();

		// 2. 构建结果Map（线程 → 新增的DKP集合）
		Map<String, Set<String>> newDKPs = new HashMap<>();

		// 3. 遍历当前Trace的每个线程
		currentDKPs.forEach((threadId, currentThreadDKPs) -> {
			// 3.1 收集所有其他Trace中该线程的DKP集合（全局存在）
			Set<String> existingDKPsForThread = traces.stream()
					.filter(trace -> trace != currentTrace) // 排除当前Trace自身（根据需求可选）
					.map(trace -> trace.getDkps().getOrDefault(threadId, Collections.emptySet()))
					.flatMap(Set::stream)
					.collect(Collectors.toSet());

			// 3.2 计算当前线程中存在但全局不存在的DKPs
			Set<String> newDKPsForThread = currentThreadDKPs.stream()
					.filter(dkp -> !existingDKPsForThread.contains(dkp))
					.collect(Collectors.toSet());

			// 3.3 如果存在新增DKP，则加入结果
			if (!newDKPsForThread.isEmpty()) {
				newDKPs.put(threadId, newDKPsForThread);
			}
		});

		return newDKPs;
	}



	/**
	 * generate new schedules from the trace by this execution
	 */
	public void completedScheduleExecution() {
		this.notYetExecutedFirstSchedule = false;

		//Vector<String> prefix = new Vector<String>();
//		for (String choice : MCRStrategy.schedulePrefix) {
//			prefix.add(choice);
//		}

		if (Configuration.DEBUG) {
			System.out.print("<< Exploring trace executed along causal schedule " + count + ": ");
			count++;
			System.err.println(choicesMade);
			System.out.print("\n");
		}

		//executeMultiThread(trace, prefix);

		/*
		 * after executing the program along the given prefix
		 * then the model checker will analyze the trace generated
		 * to computer more possible interleavings
		 */

			// 记录当前trace
		currentTrace.calDkps();
		// 检测新DKPs
		Map<String, Set<String>>DKPS=getDkps(currentTrace);
		currentTrace.setdkps(DKPS);
		currentTrace.setPeriod(p);
		Map<String, Set<String>> newDKPs = findNewDKPs(currentTrace);//此处有bug，计算方式有误

		if(!newDKPs.isEmpty()){
			// 处理新DKPs
			// 找到首个新DKP位置并切割前缀
			List<String> prefix = new ArrayList<>();
			int splitIndex = -1;

			// 遍历原始跟踪的每个节点，找到第一个属于 newDKPs 的节点
			List<AbstractNode> rawFullTrace = currentTrace.getRawFullTrace();
			for (int i = 0; i < rawFullTrace.size(); i++) {
				AbstractNode node = rawFullTrace.get(i);
				if (node instanceof IMemNode) {
					// 获取当前节点的 tid 和 label
					String tid = String.valueOf(node.getTid());
					String label = ((IMemNode) node).getLabel();

					// 检查该节点的 tid 和 label 是否属于 newDKPs
					if (newDKPs.containsKey(tid)) {
						Set<String> dkpLabels = newDKPs.get(tid);
						if (dkpLabels.contains(label)) {
							splitIndex = i; // 找到第一个匹配的节点位置
							break;
						}
					}
				}
			}

			// 如果未找到匹配的节点，直接返回
			if (splitIndex == -1) {
				System.err.println("错误：newDKPs 中的节点未在原始跟踪中找到");
				return;
			}

			// 提取 splitIndex 之前所有节点的 tidName
			for (int i = 0; i < splitIndex; i++) {
				AbstractNode node = rawFullTrace.get(i);
				if (node instanceof IMemNode) {
					// 将 tid 转换为 tidName
					long tid =node.getTid();
					String tidName = RVRunTime.threadTidNameMap.get(tid);
					prefix.add(tidName);
				}
			}

			// 执行前缀（仅线程名序列）
			executeSingleThread(new Vector<>(prefix));

		}else if (toExplore.isEmpty()){
// 处理周期递增

				p++;
				traces.removeIf(t -> t.getDkpsSize() < p);
				generatePeriodBasedSchedules();

		}
		else{
//下一个trace
		}

		traces.add(currentTrace);
	}



	// 生成周期调度
	private void generatePeriodBasedSchedules() {
		Set<Trace> validTraces = new HashSet<>();
		for (Trace trace : traces) {
			if (trace.getPeriod() <= p) {
				traces.remove(trace);
				// 从有效trace生成新调度
				List<String> prefix0=new ArrayList<>();
				List<String> dkps0 = trace.getEvents();

			}
		}
	}



	// 清理过期trace
	private void cleanUpTraces() {
		Iterator<Trace> it = traces.iterator();
		while (it.hasNext()) {
			Trace trace = it.next();
			if (trace.getPeriod() < p) {
				it.remove();
			}
		}
	}
	/**
	 * here creates a runnable object and it can then run the method 
	 * @param prefix
	 */

	private void executeSingleThread(Vector<String> prefix) {

		currentTrace.getTraceInfo().updateIdSigMap( RVGlobalStateForInstrumentation.stmtIdSigMap );   //solving the first trace initialization problem

		StartExploring causalTrace = new StartExploring(currentTrace, prefix, this.toExplore , this.p,traces);
		Thread causalTraceThread = new Thread(causalTrace);
		causalTraceThread.start();
		try {
			causalTraceThread.join();

		} catch (InterruptedException e) {
			e.printStackTrace();
		}
	}

	@SuppressWarnings("unused")
	private void executeMultiThread(Trace trace, Vector<String> prefix) {

		StartExploring causalTrace = new StartExploring(trace, prefix,
				this.toExplore,this.p);
		StartExploring.executorsCount.increase();
		MCRStrategy.executor.submit(causalTrace);
	}

	@Override
	public boolean canExecuteMoreSchedules() {
		boolean result = (!this.toExplore.isEmpty())
				|| this.notYetExecutedFirstSchedule;
		if (!result) {
			while (StartExploring.executorsCount.getValue() > 0) {
				try {
					Thread.sleep(10);
				} catch (InterruptedException e) {
					e.printStackTrace();
				}
			}
			result = (!this.toExplore.isEmpty())
					|| this.notYetExecutedFirstSchedule;
			return result;
		} else {
			return true;
		}

	}

	/**
	 * choose the next statement to execute
	 * this function needs more inspection
	 */
	@Override
	public Object choose(SortedSet<? extends Object> objectChoices, ChoiceType choiceType)
	{
		/*
		 * Initialize choice
		 */
		int chosenIndex = 0;
		Object chosenObject = null;

		//for the rest events, executed in random schedule
		if (MCRStrategy.schedulePrefix.size() > RVRunTime.currentIndex) {
			/*
			 * Make the choice to be made according to schedule prefix
			 */
			// chosenIndex = MCRStrategy.schedulePrefix
			// .get(this.currentIndex);
			chosenIndex = getChosenThread(objectChoices, RVRunTime.currentIndex);
			chosenObject = getChosenObject(chosenIndex, objectChoices);

			if (Configuration.DEBUG) {
				if (chosenObject != null)
					System.out.println(RVRunTime.currentIndex + ":" + chosenObject.toString());
			}

			if (chosenObject == null) {

				//one case that can cause this is due to the wait event
				//wait has no corresponding schedule index, it has to be announced
				//chose the wait to execute, the wait is trying to acquire the semaphore
				for (Object objectChoice : objectChoices) {
					ThreadInfo threadInfo = (ThreadInfo) objectChoice;
					if (threadInfo.getEventDesc().getEventType() == EventType.WAIT) {
						return threadInfo;
					}
				}

				//what if the chosenObject is still null??
				//it might not correct
//			    if (chosenObject == null) {
//		            chosenIndex = 0;
//		            while (true) {
//		                chosenObject = getChosenObject(chosenIndex, objectChoices);
//
//		                if(choiceType.equals(ChoiceType.THREAD_TO_FAIR)
//		                        && chosenObject.equals(previousThreadInfo))
//		                {
//		                    //change to a different thread
//		                }
//		                else
//		                    break;
//		                chosenIndex++;
//		            }
//		        }
//		        MCRStrategy.choicesMade.add(chosenIndex);
//
//		        this.previousThreadInfo = (ThreadInfo) chosenObject;
//                return chosenObject;
			}

		}

		//it might be that the wanted thread is blocked, waiting to be added to the paused threads
		if (chosenObject == null) {
			chosenIndex = 0;
			while (true) {
				chosenObject = getChosenObject(chosenIndex, objectChoices);

				if(choiceType.equals(ChoiceType.THREAD_TO_FAIR)
						&& chosenObject.equals(previousThreadInfo))
				{
					//change to a different thread
				}
				else
					break;
				chosenIndex++;

			}

		}
		MCRStrategy.choicesMade.add(chosenIndex);
		this.previousThreadInfo = (ThreadInfo) chosenObject;

		return chosenObject;
	}

	@Override
	public List<Integer> getChoicesMadeDuringThisSchedule() {
		return MCRStrategy.choicesMade;
	}


	/**
	 * chose a thread object based on the index
	 * return -1 if not found
	 * @param objectChoices set of object choices
	 * @param index the given index
	 * @return return the index of chosen thread object
	 */
	private int getChosenThread(SortedSet<? extends Object> objectChoices, int index) {
		String name = MCRStrategy.schedulePrefix.get(index).split("_")[0];
		long tid = -1;
		for (Entry<Long, String> entry : RVRunTime.threadTidNameMap.entrySet()) {
			if (name.equals(entry.getValue())) {
				tid = entry.getKey();
				break;
			}
		}

		Iterator<? extends Object> iter = objectChoices.iterator();
		int currentIndex = -1;
		while (iter.hasNext()) {
			++currentIndex;
			ThreadInfo ti = (ThreadInfo) iter.next();
			if (ti.getThread().getId() == tid) {
				return currentIndex;
			}
		}

		return -1;
	}
}
