package entities;

import java.io.Serializable;

import static java.lang.Math.abs;

public class Person implements Serializable {
    private static final long serialVersionUID = 12347568L;
    private final int id;
    private final int to;
    private int from;
    private final long recTime;
    private final long et;

    public Person(int personId, int fromFloor, int toFloor, long time) {
        this.id = personId;
        this.from = fromFloor;
        this.to = toFloor;
        this.recTime = time;
        this.et = calEt(from, to);
    }

    private long calEt(int from, int to) {
        long moveExpectation = 0;
        for (int i = 1; i <= 11; i++) {
            moveExpectation += abs(from - i) * 400L;
        }
        return 400 + abs(from - to) + moveExpectation / 11;
    }

    public int getFrom() {
        return this.from;
    }

    public int getTo() {
        return this.to;
    }

    public int getId() {
        return this.id;
    }

    public long getTime() {
        return this.recTime;
    }

    @Override
    public String toString() {
        return "[" + recTime + "]" + id + "-" + from + "-" + to;
    }

    public void setFrom(int currFloor) {
        this.from = currFloor;
    }

    public long getEt() {
        return this.et;
    }
}
