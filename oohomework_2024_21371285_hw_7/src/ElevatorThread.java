import com.oocourse.elevator3.TimableOutput;
import entities.CalPerf;
import entities.Elevator;
import entities.RequestQueue;
import entities.Scheduler;
import entities.Person;
import utils.EleAction;

import java.util.ArrayList;

public class ElevatorThread implements Runnable, CalPerf {
    private final Elevator elevator;
    private final Scheduler scheduler;
    private EleAction act;
    private final RequestQueue waitQueue;
    private final Dispatcher dispatcher;
    private boolean alreadyRun = false;
    private int[] res = new int[3];

    public ElevatorThread(Elevator ele, Scheduler sche, RequestQueue wtQueue, Dispatcher disp) {
        this.elevator = ele;
        this.scheduler = sche;
        this.waitQueue = wtQueue;
        this.dispatcher = disp;
    }

    @Override
    public synchronized void run() {
        while (scheduler.notEnd()) {
            switch (elevator.getState()) {
                case IDLE:
                    actIdle();
                    break;
                case WORK:
                    actWork();
                    break;
                default:
                    TimableOutput.println("ERROR IN ET SWITCH");
                    break;
            }
        }
        if (!scheduler.getResetType()) {
            dispatcher.replace(elevator.getId());
        }
        notifyAll();
    }

    private void actIdle() {
        act = scheduler.getNextStep();
        switch (act) {
            case UP:
                elevator.up();
                scheduler.addPerf(16, elevator.getSpeed());
                break;
            case DOWN:
                elevator.down();
                scheduler.addPerf(16, elevator.getSpeed());
                break;
            case OPEN:
                elevator.open();
                scheduler.addPerf(4, 0);
                break;
            case WAIT:
                synchronized (scheduler) {
                    scheduler.waitForRequest();
                }
                break;
            case RESET:
                ArrayList<Person> toRecycles;
                synchronized (scheduler) {
                    toRecycles = scheduler.reset();
                }
                synchronized (waitQueue) {
                    waitQueue.add(toRecycles);
                    waitQueue.doneReset();
                }
                break;
            default:
                TimableOutput.println("ERROR IN IDLE: " + act);
                break;
        }
    }

    private void actWork() {
        boolean endWork = false;
        while (!endWork) {
            act = scheduler.getNextStep();
            switch (act) {
                case OUT:
                    ArrayList<Person> toRecycles;
                    int arrived;
                    synchronized (scheduler) {
                        toRecycles = scheduler.outPerson();
                        arrived = scheduler.getArrived();
                    }
                    synchronized (waitQueue) {
                        waitQueue.add(toRecycles);
                        waitQueue.countArrived(arrived);
                    }
                    break;
                case IN:
                    synchronized (scheduler) {
                        scheduler.inPerson();
                    }
                    break;
                case CLOSE:
                    elevator.close();
                    scheduler.addPerf(4, 400);
                    endWork = true;
                    break;
                default:
                    TimableOutput.println("ERROR IN WORK: " + act);
                    break;
            }
        }
    }

    public synchronized int[] getPerformanceRes() {
        notifyAll();
        if (!alreadyRun) {
            run();
            res[0] = scheduler.getSimulatedTime();
            res[1] = scheduler.getMt();
            res[2] = scheduler.getPowerUsed();
            alreadyRun = true;
        }
        // System.out.println("#ELE: PERF DONE");
        return res;
    }
}
