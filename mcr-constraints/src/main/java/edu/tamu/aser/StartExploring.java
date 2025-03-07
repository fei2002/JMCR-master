package edu.tamu.aser;

import java.util.*;

import edu.tamu.aser.config.Configuration;
import edu.tamu.aser.trace.*;

public class StartExploring implements Runnable {

	private Trace traceObj;                        //the current trace
	private Vector<String> schedule_prefix;        //the prefix that genrates the trace
	private Queue<List<String>> exploreQueue;      //the seed interleavings
    private int period ;
	Set<Trace> traces;
	public static class BoxInt {

		volatile int  value;

		BoxInt(int initial) {
			this.value = initial;
		}

		public synchronized int getValue() {
			return this.value;
		}

		public synchronized void increase() {
			this.value++;
		}

		public synchronized void decrease() {
			this.value--;
		}
	}

	public final static BoxInt executorsCount = new BoxInt(0);

	public StartExploring(Trace trace, Vector<String> prefix, Queue<List<String>> queue ,int p) {
		this.traceObj = trace;
		this.schedule_prefix = prefix;
		this.exploreQueue = queue;
		this.period = p;
	}

	public StartExploring(Trace trace, Vector<String> prefix, Queue<List<String>> queue ,int p,Set<Trace> traces) {
		this.traceObj = trace;
		this.schedule_prefix = prefix;
		this.exploreQueue = queue;
		this.period = p;
		this.traces=traces;
	}


	private Set<String> getDkps(Trace trace) { //该方法不适合在此地
		Set<String> dkps = new HashSet<>();

		// Iterate over all events in the trace and add key points (memory accesses and sync operations)
		for (IMemNode node : trace.getAllMemoryNodes()) {
			if (node instanceof ReadNode || node instanceof WriteNode) {
				//String address = node.getAddr();
				dkps.add(String.valueOf(node.getTid())); // Add memory access events to dkps
				dkps.add(((AbstractNode) node).getLabel()); // Add memory access events to dkps

			}
		}

		// Add synchronization events (locks and unlocks)
//		for (ISyncNode node : trace.getSyncNodes()) {
//			if (node instanceof LockNode || node instanceof UnlockNode) {
//				String address = node.getAddr();
//				dkps.add("SyncEvent_" + address + "_" + node.getTid()); // Add synchronization events to dkps
//			}
//		}

		return dkps;
	}

	public Trace getTrace() {
		return this.traceObj;
	}




	/**
	 * 获取线程完整的原始事件序列（包含所有事件类型）
	 */
	private Map<String, List<String>> getFullThreadEvents(Trace trace) {
		Map<String, List<String>> threadEvents = new LinkedHashMap<>(); // 保持插入顺序

		// 遍历跟踪中的所有事件节点
		for (AbstractNode node : trace.getFullTrace()) {
			// 生成事件描述符
			String descriptor = buildEventDescriptor(node);

			// 获取线程ID并转换可读名称
			String tid = trace.getThreadIdNameMap().get(node.getTid());

			// 按线程分组存储
			threadEvents.computeIfAbsent(tid, k -> new ArrayList<>())
					.add(descriptor);
		}
		return threadEvents;
	}


	/**
	 * 构建事件描述符（增强版）
	 */
	private String buildEventDescriptor(AbstractNode node) {
		StringJoiner sj = new StringJoiner("_");

		// 公共部分：事件类型 + 线程ID
		String tid = String.valueOf(node.getTid());

		// 处理不同类型的事件
		if (node instanceof ReadNode) {
			ReadNode rn = (ReadNode) node;
			sj.add("Read")
					.add(rn.getAddr())
					.add(tid);
		} else if (node instanceof WriteNode) {
			WriteNode wn = (WriteNode) node;
			sj.add("Write")
					.add(wn.getAddr())
					.add(tid);
		} else if (node instanceof LockNode) {
			LockNode ln = (LockNode) node;
			sj.add("Lock")
					.add(ln.getAddr())
					.add(tid);
		} else if (node instanceof UnlockNode) {
			UnlockNode uln = (UnlockNode) node;
			sj.add("Unlock")
					.add(uln.getAddr())
					.add(tid);
		} else {
			// 处理其他事件类型
			sj.add(node.getClass().getSimpleName())
					.add("N/A")
					.add(tid);
		}

		return sj.toString();
	}

//	public Vector<String> getCurrentSchedulePrefix() {
//		return this.schedule_prefix;
//	}

//	public Queue<List<String>> exploreQueue() {
//		return this.exploreQueue;
//	}

	/**
	 * start exploring other interleavings
	 *
	 */
	public void run() {
		try {

			ExploreSeedInterleavings explore = new ExploreSeedInterleavings(exploreQueue,traces);

			//load the trace
			traceObj.finishedLoading(true);
			//at 这 shared var 识别
			//该方法用于生成交错
			//explore.execute(traceObj, schedule_prefix);//这个方法不用进去了
			//Map<String, List<String>> fullEvents = getFullThreadEvents(traceObj);


			explore.execute(traceObj, schedule_prefix);
//			ExploreSeedInterleavings.memUsed += ExploreSeedInterleavings.memSize(ExploreSeedInterleavings.mapPrefixEquivalent);
		} catch (Exception e) {
			e.printStackTrace();
			System.out.println(e.getMessage());
		}
		finally {
			if (Configuration.DEBUG) {
				System.out.println("  Exploration Done with this trace! >>\n\n");
			}
		}
	}
}
