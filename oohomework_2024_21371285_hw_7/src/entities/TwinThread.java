package entities;

import com.oocourse.elevator3.TimableOutput;
import utils.EleAction;

import java.util.ArrayList;

public class TwinThread implements Runnable {
    private final Elevator elevator;
    private final TwinScheduler scheduler;
    private final TwinScheduler twin;
    private final int tsFloor;
    private EleAction act;
    private final TheFloor lock;

    public TwinThread(Elevator ele, TwinScheduler sche, TheFloor lock, TwinScheduler twin) {
        this.elevator = ele;
        this.scheduler = sche;
        this.twin = twin;
        this.lock = lock;
        this.tsFloor = sche.getTsFloor();
    }

    @Override
    public synchronized void run() {
        while (lock.getNotArrived() != 0) {
            // System.out.println("#TWIN THREAD: IN LOOP");
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
        //if (scheduler.notShadow()) {
        // System.out.println("#REAL TWIN: DONE" + elevator.getId());
        //} else {
        // System.out.println("#SHADOW TWIN: DONE" + elevator.getId());
        //}
        scheduler.setEnd();
        twin.setEnd();
        notifyAll();
    }

    private synchronized void actIdle() {
        act = scheduler.getNextStep();
        // System.out.println("#TWIN THREAD: IN IDLE WITH ACT " + act);
        switch (act) {
            case UP:
                if (scheduler.notShadow() && elevator.getCurrFloor() + 1 == tsFloor) {
                    lock.get();
                    //// System.out.println(elevator.getId() + ": GOT LOCK");
                }
                elevator.up();
                if (scheduler.notShadow() && elevator.getCurrFloor() - 1 == tsFloor) {
                    lock.release();
                    //// System.out.println(elevator.getId() + ": RELEASED LOCK");
                }
                scheduler.addPerf(4, elevator.getSpeed());
                break;
            case DOWN:
                if (scheduler.notShadow() && elevator.getCurrFloor() - 1 == tsFloor) {
                    lock.get();
                    //// System.out.println(elevator.getId() + ": GOT LOCK");
                }
                elevator.down();
                if (scheduler.notShadow() && elevator.getCurrFloor() + 1 == tsFloor) {
                    lock.release();
                    //// System.out.println(elevator.getId() + ": RELEASED LOCK");
                }
                scheduler.addPerf(4, elevator.getSpeed());
                break;
            case OPEN:
                elevator.open();
                scheduler.addPerf(1, 0);
                break;
            case WAIT:
                scheduler.waitForRequest();
                break;
            default:
                TimableOutput.println("ERROR IN IDLE: " + act);
                break;
        }
    }

    private synchronized void actWork() {
        boolean endWork = false;
        while (!endWork) {
            act = scheduler.getNextStep();
            // System.out.println("#TWIN THREAD: IN WORK WITH ACT " + act);
            switch (act) {
                case OUT:
                    ArrayList<Person> toRecycles;
                    int arrived;
                    synchronized (scheduler) {
                        toRecycles = scheduler.outPerson();
                        arrived = scheduler.getArrived();
                    }
                    twin.addRequest(toRecycles);
                    lock.addArrived(arrived);
                    break;
                case IN:
                    synchronized (scheduler) {
                        scheduler.inPerson();
                    }
                    break;
                case CLOSE:
                    elevator.close();
                    scheduler.addPerf(1, 400);
                    endWork = true;
                    break;
                default:
                    TimableOutput.println("ERROR IN WORK: " + act);
                    break;
            }
        }
    }
}
