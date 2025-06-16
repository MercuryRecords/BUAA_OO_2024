package entities;

import utils.Dir;
import utils.EleState;

public class ShadowElevator extends Elevator {

    public ShadowElevator(Elevator elevator) {
        this.setDir(elevator.getDir());
        this.setId(elevator.getId());
        this.setCurrFloor(elevator.getCurrFloor());
        this.setCurrCnt(elevator.getCurrCnt());
        this.setState(elevator.getState());
        this.setLastTime(elevator.getLastTime());
        this.setCapacity(elevator.getCapacity());
        this.setSpeed(elevator.getSpeed());
        this.setToSetCapacity(elevator.getToSetCapacity());
        this.setToSetSpeed(elevator.getToSetSpeed());
        this.setBottom(elevator.getBottom());
        this.setTop(elevator.getTop());
    }

    @Override
    public synchronized void up() {
        setDir(Dir.UP);
        addFloor(1);
    }

    @Override
    public synchronized void down() {
        setDir(Dir.DOWN);
        addFloor(-1);
    }

    @Override
    public synchronized void open() {
        this.setState(EleState.WORK);
    }

    @Override
    public synchronized void close() {
        this.setState(EleState.IDLE);
    }

    @Override
    public synchronized void inPerson(int id) {
        this.currCntAdd(1);
    }

    @Override
    public synchronized void outPerson(int id) {
        this.currCntAdd(-1);
    }
}
