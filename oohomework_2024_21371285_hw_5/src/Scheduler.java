import com.oocourse.elevator1.PersonRequest;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;

import static java.lang.Math.abs;

public class Scheduler {

    private final Elevator elevator;
    private final int[] waitList = new int[12];
    private final HashMap<Integer, ArrayList<Person>> waitByFloor = new HashMap<>();
    private final HashMap<Integer, ArrayList<Person>> outByFloor = new HashMap<>();
    private boolean isEnd = false;
    private Dir reqDirection = Dir.STILL;

    public Scheduler(Elevator elevator) {
        this.elevator = elevator;
    }

    public synchronized void addRequest(PersonRequest req) {
        Person person = new Person(req.getPersonId(), req.getFromFloor(), req.getToFloor());
        addWaitIfAbsent(person, person.getFrom());
        synchronized (waitList) {
            waitList[person.getFrom()] += 1;
            waitList[0] += 1;
        }
        notifyAll();
    }

    public synchronized EleAction getNextStep() {
        if (elevator.getState() == EleState.IDLE) {
            if (elevator.isEmpty() && waitByFloor.isEmpty()) {
                return EleAction.WAIT;
            }
            if (outByFloor.containsKey(elevator.getCurrFloor()) || sameDirectionReq()) {
                return EleAction.OPEN;
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
            // 先放人
            if (outByFloor.containsKey(elevator.getCurrFloor())) {
                return EleAction.OUT;
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

    private boolean sameDirectionReq() {
        if (waitByFloor.containsKey(elevator.getCurrFloor()) && reqDirection != Dir.STILL
            && !elevator.isFull()) {
            ArrayList<Person> tmp = waitByFloor.get(elevator.getCurrFloor());
            for (Person person: tmp) {
                if (person.getTo() > elevator.getCurrFloor() && reqDirection == Dir.UP) {
                    return true;
                }
                if (person.getTo() < elevator.getCurrFloor() && reqDirection == Dir.DOWN) {
                    return true;
                }
            }
        }
        return false;
    }

    private EleAction noBodyOut() {
        synchronized (waitList) {
            if (elevator.getDir() == Dir.UP) {
                if (waitByFloor.containsKey(elevator.getCurrFloor())) {
                    for (Person person: waitByFloor.get(elevator.getCurrFloor())) {
                        if (person.getTo() > elevator.getCurrFloor()) {
                            return EleAction.OPEN;
                        }
                    }
                }
                for (int i = elevator.getCurrFloor() + 1; i <= 11; i++) {
                    if (waitList[i] > 0) {
                        return EleAction.UP;
                    }
                }
                if (waitList[elevator.getCurrFloor()] > 0) {
                    return EleAction.OPEN;
                }
                return EleAction.DOWN;
            } else {
                if (waitByFloor.containsKey(elevator.getCurrFloor())) {
                    for (Person person: waitByFloor.get(elevator.getCurrFloor())) {
                        if (person.getTo() < elevator.getCurrFloor()) {
                            return EleAction.OPEN;
                        }
                    }
                }
                for (int i = elevator.getCurrFloor() - 1; i >= 1; i--) {
                    if (waitList[i] > 0) {
                        return EleAction.DOWN;
                    }
                }
                if (waitList[elevator.getCurrFloor()] > 0) {
                    return EleAction.OPEN;
                }
                return EleAction.UP;
            }
        }
    }

    public synchronized void outPerson() { // 肯定是有人才让出
        if (elevator.isEmpty()) {
            return;
        }
        ArrayList<Person> tmp = outByFloor.get(elevator.getCurrFloor());
        Iterator<Person> it = tmp.iterator();
        while (it.hasNext()) {
            Person person = it.next();
            it.remove();
            elevator.outPerson(person.getId());
            synchronized (waitList) {
                waitList[person.getTo()] -= 1;
                waitList[0] -= 1;
            }
        }
        if (tmp.isEmpty()) {
            outByFloor.remove(elevator.getCurrFloor());
        }
        if (outByFloor.isEmpty()) {
            this.reqDirection = Dir.STILL;
        }
    }

    public synchronized void inPerson() { // 肯定是有人要进
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

    private synchronized void addOutIfAbsent(Person per, Integer asKey) {
        if (outByFloor.containsKey(asKey)) {
            ArrayList<Person> tmp = outByFloor.get(asKey);
            tmp.add(per);
        } else {
            ArrayList<Person> tmp = new ArrayList<>();
            tmp.add(per);
            outByFloor.put(asKey, tmp);
        }
    }

    private synchronized void addWaitIfAbsent(Person per, Integer asKey) {
        if (waitByFloor.containsKey(asKey)) {
            ArrayList<Person> tmp = waitByFloor.get(asKey);
            tmp.add(per);
        } else {
            ArrayList<Person> tmp = new ArrayList<>();
            tmp.add(per);
            waitByFloor.put(asKey, tmp);
        }
    }

    public synchronized void setEnd() {
        this.isEnd = true;
        notifyAll();
    }

    public synchronized boolean notEnd() {
        return !this.isEnd || !noRequest();
    }

    public synchronized boolean noRequest() {
        return waitByFloor.isEmpty() && outByFloor.isEmpty();
    }

    public synchronized void waitForRequest() {
        try {
            wait();
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }

    private synchronized Person getPerson(ArrayList<Person> tmp) {
        for (Person person: tmp) {
            if (person.getTo() > elevator.getCurrFloor() && reqDirection == Dir.UP) {
                return person;
            }
            if (person.getTo() < elevator.getCurrFloor() && reqDirection == Dir.DOWN) {
                return person;
            }
        }
        return tmp.get(0);
    }
}
