import com.oocourse.elevator3.DoubleCarResetRequest;
import entities.Controller;
import entities.DumbQueue;
import entities.RequestQueue;
import entities.Twin;
import entities.Person;
import entities.CalPerf;
import entities.Scheduler;
import entities.ShadowElevator;
import utils.SerialClone;

import java.util.HashMap;
import static java.lang.Integer.max;

public class Dispatcher implements Runnable {

    private final RequestQueue waitQueue;
    private final HashMap<Integer, Controller> queues = new HashMap<>();
    private final HashMap<Integer, Twin> toReplace = new HashMap<>();
    private int currScheduler = 6;
    private int preferred = 6;
    private int replaceCnt = 0;
    private boolean end = false;
    private final DumbQueue dq = new DumbQueue();
    private int[] cnt = new int[7];

    public Dispatcher(RequestQueue waitQueue) {
        this.waitQueue = waitQueue;
    }

    @Override
    public void run() {
        while (true) {
            Person request = waitQueue.take();
            if (request == null) {
                end = true;
                for (Controller scheduler: queues.values()) {
                    scheduler.setEnd();
                }
                break;
            } else {
                /* choose scheduler begin */
                // System.out.println("#DEBUG: BEGIN SELECT");
                currScheduler = chooseScheduler(request);
                cnt[currScheduler] += 1;
                cnt[0] += 1;
                // System.out.println("#DEBUG: DONE SELECT");
                preferred = preferred % 6 + 1;
                //waitReplaceDone();
                //currScheduler = currScheduler % 6 + 1;
                /* choose scheduler end */
                Controller toPut = queues.get(currScheduler);
                boolean flag = toPut.addRequest(request);
                while (!flag) {
                    // System.out.println("#DEBUG: IN WHILE");
                    waitReplaceDone();
                    toPut = queues.get(currScheduler);
                    flag = toPut.addRequest(request);
                }
                if (toPut instanceof Twin) {
                    waitQueue.countArrived(1);
                }
            }
            // System.out.println("#DEBUG: " + waitQueue.getSize());
        }
        // System.out.println("#DEBUG: DISPATCHER DONE");
    }

    public void add(int i, Controller scheduler) {
        this.queues.put(i, scheduler);
    }

    private int chooseScheduler(Person pr) {
        boolean noScheduler = true;
        HashMap<Integer, CalPerf> etAdd = new HashMap<>();
        HashMap<Integer, CalPerf> etNotAdd = new HashMap<>();
        waitReplaceDone();
        for (Integer index: queues.keySet()) {
            if (cnt[index] > cnt[0] / 3) {
                continue;
            }
            Controller tmpController = queues.get(index);
            synchronized (tmpController) {
                if (tmpController instanceof Scheduler) {
                    Scheduler oneCon = (Scheduler) tmpController;
                    if (oneCon.notToReset() && oneCon.notBusy() && oneCon.notEnd()) {
                        noScheduler = false;
                        Scheduler sdSche1 = SerialClone.dc(oneCon);
                        if (sdSche1 != null) {
                            ShadowElevator sdEle1 = sdSche1.toShadow(SerialClone.dc(pr));
                            ElevatorThread et1 = new ElevatorThread(sdEle1, sdSche1, dq, this);
                            etAdd.put(index, et1);
                        }
                        Scheduler sdSche0 = SerialClone.dc(oneCon);
                        if (sdSche0 != null) {
                            ShadowElevator sdEle0 = sdSche0.toShadow(null);
                            ElevatorThread et0 = new ElevatorThread(sdEle0, sdSche0, dq, this);
                            etNotAdd.put(index, et0);
                        }
                    }
                } else if (tmpController instanceof Twin) {
                    noScheduler = false;
                    Twin sdTwin0 = ((Twin) tmpController).dc();
                    Twin sdTwin1 = SerialClone.dc(sdTwin0);
                    if (sdTwin1 != null) {
                        sdTwin1.toShadow(SerialClone.dc(pr));
                        etAdd.put(index, sdTwin1);
                    }
                    if (sdTwin0 != null) {
                        sdTwin0.toShadow(null);
                        etNotAdd.put(index, sdTwin0);
                    }
                }
            }
        }
        if (noScheduler) {
            return currScheduler % 6 + 1;
        }
        HashMap<Integer, int[]> toCal = new HashMap<>();
        for (int index: etAdd.keySet()) {
            toCal.put(index, sumPerf(index, etAdd.get(index).getPerformanceRes(), etNotAdd));
        }
        int ret = select(toCal);
        for (int index: etNotAdd.keySet()) {
            if (index == ret) {
                queues.get(index).record(etAdd.get(index).getPerformanceRes());
            } else {
                queues.get(index).record(etNotAdd.get(index).getPerformanceRes());
            }
        }
        return ret;
    }

    private int select(HashMap<Integer, int[]> toCal) {
        int tmpMax = Integer.MAX_VALUE / 10;
        int[] xmin = new int[]{tmpMax, tmpMax, tmpMax};
        int[] xmax = new int[]{0, 0, 0};
        int[] avg = new int[]{0, 0, 0};
        for (int[] tmp : toCal.values()) {
            for (int i = 0; i < 3; i++) {
                xmin[i] = Math.min(xmin[i], tmp[i]);
                xmax[i] = Math.max(xmax[i], tmp[i]);
                avg[i] += tmp[i];
            }
        }
        for (int i = 0; i < 3; i++) {
            if (!toCal.isEmpty()) {
                avg[i] /= toCal.size();
            }
            xmin[i] = avg[i] + 3 * xmin[i];
            xmax[i] = avg[i] + 3 * xmax[i];
        }
        int finalIndex = 1;
        int finalScore = -1;
        for (int index : toCal.keySet()) {
            int[] tmp = toCal.get(index);
            int score = 4 * reFunc(4 * tmp[0], xmin[0], xmax[0]);
            score += reFunc(4 * tmp[1], xmin[1], xmax[1]);
            // score += reFunc(4 * tmp[2], xmin[2], xmax[2]);
            score = 100 * score - Math.abs(preferred % 6 + 1 - index);
            // System.out.println(index + ": " + score);
            if (score > finalScore) {
                finalScore = score;
                finalIndex = index;
            }
        }
        return finalIndex;
    }

    private int reFunc(int x, int baseMin, int baseMax) {
        if (4 * x <= 3 * baseMin + baseMax) {
            return 100;
        } else if (3 * baseMin + baseMax < 4 * x && x <= baseMax) {
            return (400 * (baseMax - x)) / (3 * (baseMax - baseMin));
        } else {
            return 0;
        }
    }

    private int[] sumPerf(int targetIndex, int[] res, HashMap<Integer, CalPerf> ets) {
        for (int index: ets.keySet()) {
            if (index == targetIndex) {
                continue;
            }
            int[] toAdd = ets.get(index).getPerformanceRes();
            res[0] = max(res[0], toAdd[0]);
            res[1] = max(res[1], toAdd[1]);
            res[2] += toAdd[2];
        }
        return res;
    }

    private synchronized void waitReplaceDone() {
        while (replaceCnt != 0) {
            try {
                wait();
            } catch (InterruptedException e) {
                throw new RuntimeException(e);
            }
        }
        notifyAll();
    }

    public synchronized void preReplace(int elevatorId, DoubleCarResetRequest dcRequest) {
        toReplace.put(elevatorId, new Twin(dcRequest));
        replaceCnt += 1;
        notifyAll();
    }

    public synchronized void replace(String id) {
        queues.get(Integer.valueOf(id)).setEnd();
        Twin tmpTwin = toReplace.get(Integer.valueOf(id));
        queues.replace(Integer.valueOf(id), tmpTwin);
        if (!end) {
            tmpTwin.start();
        }
        replaceCnt -= 1;
        notifyAll();
    }
}
