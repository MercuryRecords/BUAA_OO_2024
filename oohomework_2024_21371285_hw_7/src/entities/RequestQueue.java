package entities;

import com.oocourse.elevator3.PersonRequest;

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
        notifyAll();
    }

    public synchronized void add(ArrayList<Person> people) {
        this.requests.addAll(people);
        notifyAll();
    }

    public synchronized Person take() {
        notifyAll();
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
        return pr;
    }

    public synchronized void setEnd(boolean flag) {
        this.end = flag;
        notifyAll();
    }

    public synchronized void doneReset() {
        resetTimes -= 1;
        notifyAll();
    }

    public synchronized void countArrived(int arrived) {
        this.notArrived -= arrived;
        notifyAll();
    }

    public synchronized void addReset() {
        this.resetTimes += 1;
        notifyAll();
    }
}
