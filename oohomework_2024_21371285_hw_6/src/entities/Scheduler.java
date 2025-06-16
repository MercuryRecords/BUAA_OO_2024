package entities;

import com.oocourse.elevator2.TimableOutput;
import utils.Dir;
import utils.EleAction;
import utils.EleState;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;

import static java.lang.Math.abs;
import static java.lang.Long.max;
import static java.lang.Thread.sleep;

public class Scheduler implements Serializable {
    private static final long serialVersionUID = 14962387L;
    private Elevator elevator;
    private final int[] waitList = new int[12];
    private final HashMap<Integer, ArrayList<Person>> waitByFloor = new HashMap<>();
    private final HashMap<Integer, ArrayList<Person>> outByFloor = new HashMap<>();
    private boolean isEnd = false;
    private Dir reqDirection = Dir.STILL;
    private boolean toReset = false;
    private boolean alreadyMoved = false;
    private boolean releaseAll = false;
    private long startTime;
    private boolean busy = false;
    private boolean isShadow = false;
    private int sumTime = 0;
    private int arrived = 0;
    private long mt = -10000;
    private int powerUsed = 0;

    public Scheduler(Elevator elevator) {
        this.elevator = elevator;
    }

    public synchronized void addRequest(Person pr) {
        while (this.busy) {
            try {
                wait();
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }
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

    public EleAction getNextStep() {
        int currFloor = elevator.getCurrFloor();
        if (elevator.getState() == EleState.IDLE) {
            if (this.toReset) {
                return eleActionWhenReset();
            }
            if (waitList[0] == 0) {
                return EleAction.WAIT;
            }
            synchronized (outByFloor) {
                if (outByFloor.containsKey(currFloor) || sameDirectionReq()) {
                    return EleAction.OPEN;
                }
            }
            if (reqDirection == Dir.STILL) {
                return noBodyOut();
            }
            if (reqDirection == Dir.UP) {
                return EleAction.UP;
            } else {
                return EleAction.DOWN;
            }
        } else {
            if (this.toReset) {
                if (eleActionWhenReset() == EleAction.OPEN) {
                    return EleAction.OUT;
                }
                return EleAction.CLOSE;
            }
            synchronized (outByFloor) {
                if (outByFloor.containsKey(currFloor)) {
                    return EleAction.OUT;
                }
            }
            if (sameDirectionReq()) {
                return EleAction.IN;
            }
            if (reqDirection == Dir.STILL && noBodyOut() == EleAction.OPEN) {
                return EleAction.IN;
            }
            return EleAction.CLOSE;
        }
    }

    private EleAction eleActionWhenReset() {
        int currFloor = elevator.getCurrFloor();
        synchronized (outByFloor) {
            if (alreadyMoved || (!outByFloor.containsKey(currFloor + 1)
                    && !outByFloor.containsKey(currFloor - 1))) {
                this.releaseAll = true;
            }
            if (!outByFloor.isEmpty() &&
                    (outByFloor.containsKey(currFloor) || releaseAll)) {
                return EleAction.OPEN;
            }
            if (!this.alreadyMoved) {
                if (currFloor < 11 && outByFloor.containsKey(currFloor + 1)) {
                    this.alreadyMoved = true;
                    return EleAction.UP;
                }
                if (currFloor > 0 && outByFloor.containsKey(currFloor - 1)) {
                    this.alreadyMoved = true;
                    return EleAction.DOWN;
                }

            }
            return EleAction.RESET;
        }
    }

    private boolean sameDirectionReq() {
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
                for (int i = currFloor + 1; i <= 11; i++) {
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
                for (int i = currFloor - 1; i >= 1; i--) {
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
        if (elevator.isEmpty()) {
            return null;
        }
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
            if (releaseAll) {
                ret = removeAllPassengers();
                releaseAll = false;
            }
            if (outByFloor.isEmpty()) {
                this.reqDirection = Dir.STILL;
            }
            return ret;
        }
    }

    private synchronized ArrayList<Person> removeAllPassengers() {
        ArrayList<Person> toRecycles = new ArrayList<>();
        synchronized (outByFloor) {
            for (ArrayList<Person> tmp: outByFloor.values()) {
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
        notifyAll();
        return toRecycles;
    }

    public synchronized void inPerson() {
        if (elevator.isFull()) {
            return;
        }
        synchronized (waitByFloor) {
            ArrayList<Person> tmp = waitByFloor.get(elevator.getCurrFloor());
            if (tmp.isEmpty()) {
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

    public synchronized boolean notEnd() {
        notifyAll();
        return !this.isEnd || !noRequest();
    }

    public synchronized boolean noRequest() {
        return waitByFloor.isEmpty() && outByFloor.isEmpty() && waitList[0] == 0;
    }

    public synchronized void waitForRequest() {
        if (waitList[0] == 0 && !this.isEnd && !this.toReset) {
            try {
                wait();
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }
        notifyAll();
    }

    private synchronized Person getPerson(ArrayList<Person> tmp) {
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

    public synchronized void preset(int capacity, double speed) {
        // 这个应该是认为收到了reset信号，给电梯RESET动作时执行elevator.reset
        // 尽快停靠：在两次移动楼层操作内将所有乘客放出，考虑到和状态机异步，只能移动一次
        // 如果一步之内能到就到一下
        // scheduler 增加是否得进行reset的判断标志
        // 清空乘客并关门之后
        // 清空乘客：如果没到，重新编制request到queue（需要先out）
        // 1. 输出RESET_BEGIN-电梯ID -> wait(1200) -> 输出RESET_END-电梯ID
        // 2. 输出RESET_BEGIN-电梯ID -> 取消所有RECEIVE -> 重新编制request到queue（不需要out）
        elevator.preset(capacity, (int) (1000 * speed));
        this.toReset = true; // 呼应reset完要置false
        notifyAll(); // 以防在WAIT态
    }

    public synchronized ArrayList<Person> reset() {
        busy = true;
        if (!isShadow) {
            TimableOutput.println("RESET_BEGIN-" + elevator.getId());
            startTime = System.currentTimeMillis();
        }
        ArrayList<Person> toRecycles = new ArrayList<>();
        for (ArrayList<Person> tmp: waitByFloor.values()) {
            for (Person tmpPerson: tmp) {
                toRecycles.add(tmpPerson);
                waitList[tmpPerson.getFrom()] -= 1;
                waitList[0] -= 1;
            }
        }
        waitByFloor.clear();
        elevator.reset();
        toReset = alreadyMoved = releaseAll = false;
        if (!isShadow) {
            long endTime = System.currentTimeMillis();
            if (endTime - startTime < 1200) {
                try {
                    sleep(1200 - endTime + startTime);
                } catch (InterruptedException e) {
                    e.printStackTrace();
                }
            }
            TimableOutput.println("RESET_END-" + elevator.getId());
        } else {
            sumTime += 1200;
        }
        busy = false;
        notifyAll();
        return toRecycles;
    }

    public synchronized ShadowElevator toShadow() {
        this.isShadow = true;
        this.sumTime = 0;
        this.elevator = new ShadowElevator(this.elevator);
        notifyAll();
        return (ShadowElevator) this.elevator;
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

    public boolean notToReset() {
        return !this.toReset;
    }

    public boolean notBusy() {
        return !this.busy;
    }

    public synchronized void addPowerUsed(int i) {
        this.powerUsed += i;
    }

    public int getMt() {
        return (int) this.mt;
    }

    public int getPowerUsed() {
        return this.powerUsed;
    }
}
