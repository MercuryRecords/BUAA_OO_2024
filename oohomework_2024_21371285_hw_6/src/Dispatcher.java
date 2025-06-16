import entities.*;
import utils.SerialClone;

import java.util.Arrays;
import java.util.HashMap;

import static java.lang.Integer.max;

public class Dispatcher implements Runnable {

    private final RequestQueue waitQueue;
    private final HashMap<Integer, Scheduler> queues = new HashMap<>();
    private int currScheduler = 6;
    private int requestCnt = 0;

    public Dispatcher(RequestQueue waitQueue) {
        this.waitQueue = waitQueue;
    }

    @Override
    public void run() {
        while (true) {
            Person request = waitQueue.take();
            if (request == null) {
                for (Scheduler scheduler: queues.values()) {
                    scheduler.setEnd();
                }
                break;
            } else {
                /* choose scheduler begin */
                requestCnt += 1;
                if (requestCnt <= 70) {
                    currScheduler = chooseScheduler(request);
                } else {
                    currScheduler = currScheduler % 6 + 1;
                }
                /* choose scheduler end */
                Scheduler toPut = queues.get(currScheduler);
                synchronized (toPut) {
                    toPut.addRequest(request);
                }
            }
        }
    }

    public void add(int i, Scheduler scheduler) {
        this.queues.put(i, scheduler);
    }

    private int chooseScheduler(Person person) {
        boolean noScheduler = true;
        DumbQueue dq = new DumbQueue();
        HashMap<Integer, ElevatorThread> etAdd = new HashMap<>();
        HashMap<Integer, ElevatorThread> etNotAdd = new HashMap<>();
        for (Integer index: queues.keySet()) {
            Scheduler tmpScheduler = queues.get(index);
            synchronized (tmpScheduler) {
                if (tmpScheduler.notToReset() && tmpScheduler.notBusy()) {
                    noScheduler = false;
                    Scheduler sdScheduler1 = SerialClone.deepClone(tmpScheduler);
                    if (sdScheduler1 != null) {
                        synchronized (sdScheduler1) {
                            sdScheduler1.setEnd();
                            ShadowElevator sdElevator1 = sdScheduler1.toShadow();
                            sdScheduler1.addRequest(person); // 区别是加了请求
                            ElevatorThread et1 = new ElevatorThread(sdElevator1, sdScheduler1, dq);
                            etAdd.put(index, et1);
                        }
                    }
                    Scheduler sdScheduler0 = SerialClone.deepClone(tmpScheduler);
                    if (sdScheduler0 != null) {
                        synchronized (sdScheduler0) {
                            sdScheduler0.setEnd();
                            ShadowElevator sdElevator0 = sdScheduler0.toShadow();
                            ElevatorThread et0 = new ElevatorThread(sdElevator0, sdScheduler0, dq);
                            etNotAdd.put(index, et0);
                        }
                    }
                }
            }
        }
        if (noScheduler) {
            return currScheduler % 6 + 1;
        }
        for (int index: etAdd.keySet()) {
            new Thread(etAdd.get(index)).start();
            new Thread(etNotAdd.get(index)).start();
        }
        HashMap<Integer, int[]> toCal = new HashMap<>();
        for (int index: etAdd.keySet()) {
            toCal.put(index, sumPerf(index, etAdd.get(index).getPerformanceRes(), etNotAdd));
        }
        System.out.println("NoAdding: ");
        for (int index: etNotAdd.keySet()) {
            System.out.println(index + ": " + Arrays.toString(etNotAdd.get(index).getPerformanceRes()));
        }
        System.out.println("Adding: ");
        for (int index: etAdd.keySet()) {
            System.out.println(index + ": " + Arrays.toString(etAdd.get(index).getPerformanceRes()));
        }

        return select(toCal);
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
            score +=  reFunc(4 * tmp[1], xmin[1], xmax[1]);
            score +=  reFunc(4 * tmp[2], xmin[2], xmax[2]);
            if ((score * 100) + index > finalScore) {
                finalScore = (score * 100) + index;
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

    private int[] sumPerf(int targetIndex, int[] res, HashMap<Integer, ElevatorThread> ets) {
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
}
