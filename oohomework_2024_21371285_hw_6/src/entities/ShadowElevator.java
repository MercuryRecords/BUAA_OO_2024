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
    }

    @Override
    public synchronized void up() {
        setDir(Dir.UP);
        addSimulatedTime(getSpeed());
        addFloor(1);
    }

    @Override
    public synchronized void down() {
        setDir(Dir.DOWN);
        addSimulatedTime(getSpeed());
        addFloor(-1);
    }

    @Override
    public synchronized void open() {
        this.setState(EleState.WORK);
    }

    @Override
    public synchronized void close() {
        this.setState(EleState.IDLE);
        addSimulatedTime(400);
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
