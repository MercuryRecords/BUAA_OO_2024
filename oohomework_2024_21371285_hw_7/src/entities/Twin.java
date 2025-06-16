package entities;

import com.oocourse.elevator3.DoubleCarResetRequest;
import utils.SerialClone;

import java.io.Serializable;

public class Twin implements Controller, CalPerf, Serializable {
    private static final long serialVersionUID = 12346789L;
    private Elevator elevatorA;
    private Elevator elevatorB;
    private final TwinScheduler schedulerA;
    private final TwinScheduler schedulerB;
    private final int transferFloor;
    private final TheFloor lock = new TheFloor();
    private final int [] res = new int[3];
    private transient TwinThread etA; // 不会被克隆
    private transient TwinThread etB; // 不会被克隆
    private boolean recorded;

    public Twin(DoubleCarResetRequest dcRequest) {
        int id = dcRequest.getElevatorId();
        this.transferFloor = dcRequest.getTransferFloor();
        this.elevatorA = new Elevator(id + "-A", 1, transferFloor, transferFloor - 1);
        this.elevatorB = new Elevator(id + "-B", transferFloor, 11, transferFloor + 1);
        int cap = dcRequest.getCapacity();
        elevatorA.setCapacity(cap);
        elevatorB.setCapacity(cap);
        int speed = (int) (1000 * dcRequest.getSpeed());
        elevatorA.setSpeed(speed);
        elevatorB.setSpeed(speed);
        schedulerA = new TwinScheduler(elevatorA, transferFloor, true);
        schedulerB = new TwinScheduler(elevatorB, transferFloor, false);
        etA = new TwinThread(elevatorA, schedulerA, lock, schedulerB);
        etB = new TwinThread(elevatorB, schedulerB, lock, schedulerA);
    }

    public synchronized Twin dc() {
        synchronized (schedulerA) {
            synchronized (schedulerB) {
                return SerialClone.dc(this);
            }
        }
    }

    public synchronized void toShadow(Person person) {
        this.elevatorA = schedulerA.toShadow();
        this.elevatorB = schedulerB.toShadow();
        lock.toShadow();
        etA = new TwinThread(elevatorA, schedulerA, lock, schedulerB);
        etB = new TwinThread(elevatorB, schedulerB, lock, schedulerA);
        if (person != null) {
            addRequest(person);
        }
        setEnd();
        start();
        // System.out.println("#DEBUG: BEGIN WAIT A");
        schedulerA.waitEnd();
        // System.out.println("#DEBUG: BEGIN WAIT B");
        schedulerB.waitEnd();
        // System.out.println("#DEBUG: WAIT END");
    }

    public synchronized void start() {
        new Thread(etA, "Twin-A").start();
        new Thread(etB, "Twin-B").start();
    }

    @Override
    public synchronized void setEnd() {
        lock.setEnd();
        notifyAll();
    }

    @Override
    public synchronized boolean addRequest(Person person) {
        if (person.getFrom() == transferFloor) {
            if (person.getTo() < transferFloor) {
                schedulerA.addRequest(person);
            } else {
                schedulerB.addRequest(person);
            }
        } else if (person.getFrom() < transferFloor) {
            schedulerA.addRequest(person);
        } else {
            schedulerB.addRequest(person);
        }
        recorded = false;
        schedulerA.setRecorded(false);
        schedulerB.setRecorded(false);
        lock.addNotArrived();
        return true;
    }

    @Override
    public synchronized void record(int[] performanceRes) {
        res[0] = performanceRes[0];
        res[1] = performanceRes[1];
        res[2] = performanceRes[2];
        this.recorded = true;
        schedulerA.setRecorded(true);
        schedulerB.setRecorded(true);
        notifyAll();
    }

    @Override
    public synchronized int[] getPerformanceRes() {
        // System.out.println("#TWIN: PERF BEGIN");
        if (!recorded) {
            res[0] = schedulerA.getSimulatedTime() + schedulerB.getSimulatedTime();
            res[1] = Math.max(schedulerA.getMt(), schedulerB.getMt());
            res[2] = schedulerA.getPowerUsed() + schedulerB.getPowerUsed();
        }
        // System.out.println("#TWIN: PERF DONE");
        return res;
    }
}
