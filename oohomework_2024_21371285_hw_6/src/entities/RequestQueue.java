package entities;

import com.oocourse.elevator2.PersonRequest;

import java.io.Serializable;
import java.util.ArrayList;

public class RequestQueue implements Serializable {
    private static final long serialVersionUID = 17283456L;

    private final ArrayList<Person> requests;
    private int resetTimes = 0;
    private boolean end;
    private int notArrived = 0;

    public RequestQueue() {
        this.requests = new ArrayList<>();
        this.end = false;
    }

    public synchronized void add(PersonRequest pr) {
        long tmpTime = System.currentTimeMillis();
        Person tmp = new Person(pr.getPersonId(), pr.getFromFloor(), pr.getToFloor(), tmpTime);
        this.requests.add(tmp);
        notArrived += 1;
        notify();
    }

    public synchronized void add(ArrayList<Person> people) {
        this.requests.addAll(people);
        notify();
    }

    public synchronized Person take() {
        while (requests.isEmpty() && (!this.end || this.resetTimes != 0 || notArrived != 0)) {
            try {
                wait();
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }

        if (requests.isEmpty()) {
            return null;
        }
        Person pr = requests.get(0);
        requests.remove(0);
        notify();
        return pr;
    }

    public synchronized void setEnd(boolean flag) {
        this.end = flag;
        notify();
    }

    public synchronized void doneReset() {
        resetTimes -= 1;
        notify();
    }

    public synchronized void countArrived(int arrived) {
        this.notArrived -= arrived;
        notify();
    }

    public synchronized void addReset() {
        this.resetTimes += 1;
        notify();
    }
}
