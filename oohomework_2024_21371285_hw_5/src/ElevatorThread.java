import com.oocourse.elevator1.TimableOutput;

public class ElevatorThread implements Runnable {
    private final Elevator elevator;
    private final Scheduler scheduler;
    private EleAction act;

    public ElevatorThread(Elevator elevator, Scheduler scheduler) {
        this.elevator = elevator;
        this.scheduler = scheduler;
    }

    @Override
    public void run() {
        while (scheduler.notEnd()) {
            switch (elevator.getState()) {
                case IDLE:
                    act = scheduler.getNextStep();
                    switch (act) {
                        case UP:
                            elevator.up();
                            break;
                        case DOWN:
                            elevator.down();
                            break;
                        case OPEN:
                            elevator.open();
                            break;
                        case WAIT:
                            while (scheduler.noRequest() && scheduler.notEnd()) {
                                scheduler.waitForRequest();
                            }
                            break;
                        default:
                            TimableOutput.println("ERROR IN IDLE: " + act);
                            break;
                    }
                    break;
                case WORK: // 门开了
                    boolean endWork = false;
                    while (!endWork) {
                        act = scheduler.getNextStep();
                        switch (act) {
                            case OUT:
                                scheduler.outPerson();
                                break;
                            case IN:
                                scheduler.inPerson();
                                break;
                            case CLOSE:
                                elevator.close();
                                endWork = true;
                                break;
                            default:
                                TimableOutput.println("ERROR IN WORK: " + act);
                                break;
                        }
                    }
                    break;
                default:
                    TimableOutput.println("ERROR IN ET SWITCH");
                    break;
            }
        }
    }
}
