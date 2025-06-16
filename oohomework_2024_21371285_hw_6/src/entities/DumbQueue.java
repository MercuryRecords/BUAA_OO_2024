package entities;

import java.util.ArrayList;

public class DumbQueue extends RequestQueue {
    public DumbQueue() {
        super();
        setEnd(true);
    }

    public synchronized void add(ArrayList<Person> people) {
    }

    public synchronized void doneReset() {
    }

    public synchronized void countArrived(int arrived) {
    }
}
