import com.oocourse.elevator1.TimableOutput;

public class Elevator {
    private Dir dir = Dir.STILL;
    private final int eleId;
    private int currFloor = 1;
    private int currCnt = 0;
    private EleState state = EleState.IDLE;
    private long lastTime;

    public Elevator(int i) {
        this.eleId = i;
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
        return 6 <= this.currCnt;
    }

    public synchronized EleState getState() {
        return this.state;
    }

    public synchronized void up() {
        setDir(Dir.UP);
        try {
            wait(400);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
        this.currFloor += 1;
        arrive();
    }

    public synchronized void down() {
        setDir(Dir.DOWN);
        try {
            wait(400);
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
}
