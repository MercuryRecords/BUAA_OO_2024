package entities;

import com.oocourse.elevator3.TimableOutput;
import utils.Dir;
import utils.EleAction;
import utils.EleState;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Comparator;

import static java.lang.Long.max;
import static java.lang.Math.abs;

public class TwinScheduler implements Serializable {
    private static final long serialVersionUID = 32564789L;
    private Elevator elevator;
    private final int[] waitList = new int[12];
    private final HashMap<Integer, ArrayList<Person>> waitByFloor = new HashMap<>();
    private final HashMap<Integer, ArrayList<Person>> outByFloor = new HashMap<>();
    private boolean isEnd = false;
    private Dir reqDirection = Dir.STILL;
    private boolean isShadow = false;
    private int sumTime = 0;
    private int arrived = 0;
    private long mt = 0;
    private int powerUsed = 0;
    private final int transferFloor;
    private final boolean isA;
    private boolean recorded;

    public TwinScheduler(Elevator elevator, int tsFloor, boolean b) {
        this.elevator = elevator;
        this.transferFloor = tsFloor;
        this.isA = b;
    }

    public synchronized void addRequest(Person pr) {
        if (!isShadow) {
            TimableOutput.println("RECEIVE-" + pr.getId() + '-' + elevator.getId());
        }
        addWaitIfAbsent(pr, pr.getFrom());
        synchronized (waitList) {
            waitList[pr.getFrom()] += 1;
            waitList[0] += 1;
        }
        notifyAll();
    }

    public synchronized void addRequest(ArrayList<Person> toRecycles) {
        if (toRecycles != null) {
            for (Person pr: toRecycles) {
                addRequest(pr);
            }
        }
        notifyAll();
    }

    public synchronized EleAction getNextStep() {
        notifyAll();
        int currFloor = elevator.getCurrFloor();
        if (elevator.getState() == EleState.IDLE) {
            if (waitList[0] == 0) {
                if (currFloor == transferFloor && isA) {
                    return EleAction.DOWN;
                } else if (currFloor == transferFloor) {
                    return EleAction.UP;
                }
                return EleAction.WAIT;
            }
            synchronized (outByFloor) {
                if (outByFloor.containsKey(currFloor) || sameDirReq()) {
                    return EleAction.OPEN;
                }
            }
            if (reqDirection == Dir.STILL) {
                return noBodyOut();
            }
            if (reqDirection == Dir.UP && currFloor != elevator.getTop()) {
                return EleAction.UP;
            } else if (reqDirection == Dir.DOWN && currFloor != elevator.getBottom()) {
                return EleAction.DOWN;
            } else if (hasOS()) { // 越界的请求要放下去
                return EleAction.OPEN;
            }
            return EleAction.WAIT;
        } else {
            synchronized (outByFloor) {
                if (outByFloor.containsKey(currFloor) || (currFloor == transferFloor && hasOS())) {
                    return EleAction.OUT;
                }
            }
            if (sameDirReq() || (reqDirection == Dir.STILL && noBodyOut() == EleAction.OPEN)) {
                return EleAction.IN;
            }
            return EleAction.CLOSE;
        }
    }

    private boolean hasOS() {
        synchronized (outByFloor) {
            for (int index: outByFloor.keySet()) {
                if ((isA && index > transferFloor) || (!isA && index < transferFloor)) {
                    return true;
                }
            }
            return false;
        }
    }

    private boolean sameDirReq() {
        int currFloor = elevator.getCurrFloor();
        boolean notFull = !elevator.isFull();
        synchronized (waitByFloor) {
            if (waitByFloor.containsKey(currFloor) && reqDirection != Dir.STILL
                    && notFull) {
                ArrayList<Person> tmp = waitByFloor.get(currFloor);
                for (Person person: tmp) {
                    if (person.getTo() > currFloor && reqDirection == Dir.UP) {
                        return true;
                    }
                    if (person.getTo() < currFloor && reqDirection == Dir.DOWN) {
                        return true;
                    }
                }
            }
        }
        return false;
    }

    private EleAction noBodyOut() {
        int currFloor = elevator.getCurrFloor();
        synchronized (waitList) {
            if (elevator.getDir() == Dir.UP) {
                synchronized (waitByFloor) {
                    if (waitByFloor.containsKey(currFloor)) {
                        for (Person person: waitByFloor.get(currFloor)) {
                            if (person.getTo() > currFloor) {
                                return EleAction.OPEN;
                            }
                        }
                    }
                }
                for (int i = currFloor + 1; i <= elevator.getTop(); i++) {
                    if (waitList[i] > 0) {
                        return EleAction.UP;
                    }
                }
                if (waitList[currFloor] > 0) {
                    return EleAction.OPEN;
                }
                return EleAction.DOWN;
            } else {
                synchronized (waitByFloor) {
                    if (waitByFloor.containsKey(currFloor)) {
                        for (Person person: waitByFloor.get(currFloor)) {
                            if (person.getTo() < currFloor) {
                                return EleAction.OPEN;
                            }
                        }
                    }
                }
                for (int i = currFloor - 1; i >= elevator.getBottom(); i--) {
                    if (waitList[i] > 0) {
                        return EleAction.DOWN;
                    }
                }
                if (waitList[currFloor] > 0) {
                    return EleAction.OPEN;
                }
                return EleAction.UP;
            }
        }
    }

    public synchronized ArrayList<Person> outPerson() {
        notifyAll();
        int currFloor = elevator.getCurrFloor();
        synchronized (outByFloor) {
            if (outByFloor.containsKey(currFloor)) {
                ArrayList<Person> tmp = outByFloor.get(currFloor);
                Iterator<Person> it = tmp.iterator();
                long currTime = System.currentTimeMillis();
                while (it.hasNext()) {
                    Person person = it.next();
                    it.remove();
                    elevator.outPerson(person.getId());
                    if (person.getTo() == currFloor) {
                        arrived += 1;
                        mt = max(mt, currTime - person.getTime() - person.getEt());
                    }
                    synchronized (waitList) {
                        waitList[person.getTo()] -= 1;
                        waitList[0] -= 1;
                    }
                }
                if (tmp.isEmpty()) {
                    outByFloor.remove(currFloor);
                }
            }
            ArrayList<Person> ret = new ArrayList<>();
            if (currFloor == transferFloor) {
                ret = removeAllOtherSide();
            }
            if (outByFloor.isEmpty()) {
                this.reqDirection = Dir.STILL;
            }
            return ret;
        }
    }

    private synchronized ArrayList<Person> removeAllOtherSide() {
        notifyAll();
        ArrayList<Person> toRecycles = new ArrayList<>();
        synchronized (outByFloor) {
            for (int index: outByFloor.keySet()) {
                if (!((isA && index > transferFloor) || (!isA && index < transferFloor))) {
                    continue;
                }
                ArrayList<Person> tmp = outByFloor.get(index);
                for (Person tmpPerson: tmp) {
                    tmpPerson.setFrom(elevator.getCurrFloor());
                    toRecycles.add(tmpPerson);
                    synchronized (waitList) {
                        waitList[tmpPerson.getTo()] -= 1;
                        waitList[0] -= 1;
                    }
                    elevator.outPerson(tmpPerson.getId());
                }
            }
            outByFloor.clear();
        }
        return toRecycles;

    }

    public synchronized void inPerson() {
        notifyAll();
        if (elevator.isFull()) {
            return;
        }
        synchronized (waitByFloor) {
            ArrayList<Person> tmp = waitByFloor.get(elevator.getCurrFloor());
            if (tmp == null || tmp.isEmpty()) {
                return;
            }
            if (this.reqDirection == Dir.UP) {
                tmp.sort((a, b) -> b.getTo() - a.getTo());
            } else if (this.reqDirection == Dir.DOWN) {
                tmp.sort(Comparator.comparingInt(Person::getTo));
            } else {
                tmp.sort(Comparator.comparingInt(a -> abs(a.getTo() - 6)));
            }
            if (elevator.isEmpty()) {
                Person first = getPerson(tmp);
                if (first.getTo() > first.getFrom()) {
                    this.reqDirection = Dir.UP;
                } else {
                    this.reqDirection = Dir.DOWN;
                }
                elevator.setDir(this.reqDirection);
                addOutIfAbsent(first, first.getTo());
                elevator.inPerson(first.getId());
                tmp.remove(first);
                synchronized (waitList) {
                    waitList[first.getFrom()] -= 1;
                    waitList[first.getTo()] += 1;
                }
                if (tmp.isEmpty()) {
                    waitByFloor.remove(elevator.getCurrFloor());
                    return;
                }
            }
            Iterator<Person> it = tmp.iterator();
            while (it.hasNext() && !elevator.isFull()) {
                Person person = it.next();
                if ((person.getTo() > person.getFrom() && elevator.getDir() == Dir.UP) ||
                        (person.getTo() < person.getFrom() && elevator.getDir() == Dir.DOWN)) {
                    addOutIfAbsent(person, person.getTo());
                    it.remove();
                    elevator.inPerson(person.getId());
                    synchronized (waitList) {
                        waitList[person.getFrom()] -= 1;
                        waitList[person.getTo()] += 1;
                    }
                }
            }
            if (tmp.isEmpty()) {
                waitByFloor.remove(elevator.getCurrFloor());
            }
        }
    }

    private void addOutIfAbsent(Person per, Integer asKey) {
        synchronized (outByFloor) {
            if (outByFloor.containsKey(asKey)) {
                ArrayList<Person> tmp = outByFloor.get(asKey);
                tmp.add(per);
            } else {
                ArrayList<Person> tmp = new ArrayList<>();
                tmp.add(per);
                outByFloor.put(asKey, tmp);
            }
        }
    }

    private void addWaitIfAbsent(Person per, Integer asKey) {
        synchronized (waitByFloor) {
            if (waitByFloor.containsKey(asKey)) {
                ArrayList<Person> tmp = waitByFloor.get(asKey);
                tmp.add(per);
            } else {
                ArrayList<Person> tmp = new ArrayList<>();
                tmp.add(per);
                waitByFloor.put(asKey, tmp);
            }
        }
    }

    public synchronized void setEnd() {
        this.isEnd = true;
        notifyAll();
    }

    public synchronized void waitForRequest() {
        if (waitList[0] == 0 && !this.isEnd) {
            try {
                if (isShadow) {
                    wait(500);
                } else {
                    wait();
                }
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }
        notifyAll();
    }

    private synchronized Person getPerson(ArrayList<Person> tmp) {
        notifyAll();
        int currFloor = elevator.getCurrFloor();
        for (Person person: tmp) {
            if (person.getTo() > currFloor && reqDirection == Dir.UP) {
                return person;
            }
            if (person.getTo() < currFloor && reqDirection == Dir.DOWN) {
                return person;
            }
        }
        return tmp.get(0);
    }

    public synchronized Elevator toShadow() {
        this.sumTime = 0;
        this.powerUsed = 0;
        this.isShadow = true;
        this.elevator = new ShadowElevator(elevator);
        notifyAll();
        return this.elevator;
    }

    public synchronized int getSimulatedTime() {
        notifyAll();
        return this.sumTime;
    }

    public synchronized int getArrived() {
        int ret = this.arrived;
        this.arrived = 0;
        notifyAll();
        return ret;
    }

    public void addPerf(int powerUsed, int timeUsed) {
        this.powerUsed += powerUsed;
        this.sumTime += timeUsed;
    }

    public int getMt() {
        return (int) this.mt;
    }

    public int getPowerUsed() {
        return this.powerUsed;
    }

    public int getTsFloor() {
        return this.transferFloor;
    }

    public boolean notShadow() {
        return !this.isShadow;
    }

    public synchronized void waitEnd() {
        notifyAll();
        if (isShadow && recorded) {
            return;
        }
        if (!isEnd) {
            try {
                wait(500);
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }
        if (!isEnd) {
            sumTime = powerUsed = (int) (mt = Integer.MAX_VALUE / 10);
        }
    }

    public synchronized void setRecorded(boolean b) {
        this.recorded = b;
        notifyAll();
    }
}
