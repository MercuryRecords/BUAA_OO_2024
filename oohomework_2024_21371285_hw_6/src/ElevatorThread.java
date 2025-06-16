import com.oocourse.elevator2.TimableOutput;
import entities.Elevator;
import entities.Person;
import entities.RequestQueue;
import entities.Scheduler;
import utils.EleAction;

import java.util.ArrayList;

public class ElevatorThread implements Runnable {
    private final Elevator elevator;
    private final Scheduler scheduler;
    private EleAction act;
    private final RequestQueue waitQueue;
    private int[] res = new int[3];

    public ElevatorThread(Elevator elevator, Scheduler scheduler, RequestQueue waitQueue) {
        this.elevator = elevator;
        this.scheduler = scheduler;
        this.waitQueue = waitQueue;
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
        notifyAll();
        res[0] = (scheduler.getSimulatedTime() + elevator.getSimulatedTime());
        res[1] = scheduler.getMt();
        res[2] = scheduler.getPowerUsed();
    }

    private void actIdle() {
        act = scheduler.getNextStep();
        switch (act) {
            case UP:
                elevator.up();
                scheduler.addPowerUsed(4);
                break;
            case DOWN:
                elevator.down();
                scheduler.addPowerUsed(4);
                break;
            case OPEN:
                elevator.open();
                scheduler.addPowerUsed(1);
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
                    scheduler.addPowerUsed(1);
                    endWork = true;
                    break;
                default:
                    TimableOutput.println("ERROR IN WORK: " + act);
                    break;
            }
        }
    }

    public synchronized int[] getPerformanceRes() {
        if (scheduler.notEnd()) {
            try {
                wait();
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }
        notifyAll();
        return res;
    }
}
