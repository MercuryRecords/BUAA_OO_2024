package entities;

import java.io.Serializable;
import java.util.concurrent.locks.ReentrantReadWriteLock;

public class TheFloor implements Serializable {
    private static final long serialVersionUID = 23894756L;
    private volatile boolean occupied;
    private int notArrived = 0;
    private boolean notEnd = true;
    private final ReentrantReadWriteLock.WriteLock writeLock;
    private boolean isShadow = false;

    public TheFloor() {
        this.occupied = false;
        ReentrantReadWriteLock lock = new ReentrantReadWriteLock();
        writeLock = lock.writeLock();
    }

    public synchronized void get() {
        while (occupied) {
            try {
                wait();
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }
        occupied = true;
        notifyAll();
    }

    public synchronized void release() {
        occupied = false;
        notifyAll();
    }

    public synchronized int getNotArrived() {
        while (notArrived == 0 && notEnd) {
            try {
                if (isShadow) {
                    wait(1000);
                } else {
                    wait();
                }
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }
        notifyAll();
        if (isShadow) {
            return 0;
        } else {
            return notArrived;
        }
    }

    public synchronized void setEnd() {
        notEnd = false;
        notifyAll();
    }

    public synchronized void addNotArrived() {
        writeLock.lock();
        notArrived += 1;
        writeLock.unlock();
        notifyAll();
    }

    public synchronized void addArrived(int i) {
        writeLock.lock();
        notArrived -= i;
        writeLock.unlock();
        notifyAll();
    }

    public synchronized void toShadow() {
        this.isShadow = true;
        notifyAll();
    }
}
