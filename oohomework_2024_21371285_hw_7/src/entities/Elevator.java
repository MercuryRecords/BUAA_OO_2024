package entities;

import com.oocourse.elevator3.TimableOutput;
import utils.Dir;
import utils.EleState;

import java.io.Serializable;

public class Elevator implements Serializable {
    private static final long serialVersionUID = 14263578L;
    private Dir dir = Dir.STILL;
    private String eleId;
    private int currFloor = 1;
    private int currCnt = 0;
    private EleState state = EleState.IDLE;
    private long lastTime;
    private int capacity = 6;
    private int speed = 400;
    private int toSetCapacity;
    private int toSetSpeed;
    private int top = 11;
    private int bottom = 1;

    public Elevator(String i) {
        this.eleId = i;
    }

    public Elevator(String i, int bottom, int top, int curr) {
        this.eleId = i;
        this.bottom = bottom;
        this.top = top;
        this.currFloor = curr;
    }

    public Elevator() {
    }

    public synchronized Dir getDir() {
        return this.dir;
    }

    public synchronized void setDir(Dir dir) {
        this.dir = dir;
    }

    public synchronized int getCurrFloor() {
        return this.currFloor;
    }

    public synchronized boolean isFull() {
        return this.capacity <= this.currCnt;
    }

    public synchronized EleState getState() {
        return this.state;
    }

    public synchronized void up() {
        setDir(Dir.UP);
        try {
            wait(speed);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
        this.currFloor += 1;
        arrive();
    }

    public synchronized void down() {
        setDir(Dir.DOWN);
        try {
            wait(speed);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
        this.currFloor -= 1;
        arrive();
    }

    public synchronized void arrive() {
        TimableOutput.println("ARRIVE-" + currFloor + "-" + eleId);
    }

    public synchronized void open() {
        TimableOutput.println("OPEN-" + currFloor + "-" + eleId);
        state = EleState.WORK;
        lastTime = System.currentTimeMillis();
    }

    public synchronized void close() {
        state = EleState.IDLE;
        long currentTime = System.currentTimeMillis();
        if (currentTime - lastTime < 400) {
            try {
                wait(400 - currentTime + lastTime);
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }
        lastTime = currentTime;
        TimableOutput.println("CLOSE-" + currFloor + "-" + eleId);
    }

    public synchronized void inPerson(int id) {
        this.currCnt += 1;
        TimableOutput.println("IN-" + id + "-" + currFloor + "-" + eleId);
    }

    public synchronized boolean isEmpty() {
        return this.currCnt == 0;
    }

    public synchronized void outPerson(int id) {
        this.currCnt -= 1;
        TimableOutput.println("OUT-" + id + "-" + currFloor + "-" + eleId);
    }

    public synchronized void preset(int capacity, int speed) {
        this.toSetCapacity = capacity;
        this.toSetSpeed = speed;
    }

    public synchronized void reset() {
        this.speed = this.toSetSpeed;
        this.capacity = this.toSetCapacity;
    }

    public synchronized String getId() {
        return this.eleId;
    }

    public synchronized int getSpeed() {
        return this.speed;
    }

    protected synchronized void addFloor(int i) {
        this.currFloor += i;
    }

    protected synchronized void setState(EleState state) {
        this.state = state;
    }

    protected synchronized void currCntAdd(int i) {
        this.currCnt += i;
    }

    protected void setId(String id) {
        this.eleId = id;
    }

    protected void setCurrFloor(int currFloor) {
        this.currFloor = currFloor;
    }

    protected int getCurrCnt() {
        return this.currCnt;
    }

    protected void setCurrCnt(int currCnt) {
        this.currCnt = currCnt;
    }

    protected long getLastTime() {
        return this.lastTime;
    }

    protected void setLastTime(long lastTime) {
        this.lastTime = lastTime;
    }

    protected int getCapacity() {
        return this.capacity;
    }

    protected void setCapacity(int capacity) {
        this.capacity = capacity;
    }

    protected void setSpeed(int speed) {
        this.speed = speed;
    }

    protected int getToSetSpeed() {
        return this.toSetSpeed;
    }

    protected void setToSetSpeed(int toSetSpeed) {
        this.toSetSpeed = toSetSpeed;
    }

    protected int getToSetCapacity() {
        return this.toSetCapacity;
    }

    protected void setToSetCapacity(int toSetCapacity) {
        this.toSetCapacity = toSetCapacity;
    }

    public int getTop() {
        return this.top;
    }

    public int getBottom() {
        return this.bottom;
    }

    protected void setBottom(int bottom) {
        this.bottom = bottom;
    }

    protected void setTop(int top) {
        this.top = top;
    }
}
