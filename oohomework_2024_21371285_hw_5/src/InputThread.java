import com.oocourse.elevator1.ElevatorInput;
import com.oocourse.elevator1.PersonRequest;
import java.io.IOException;

class InputThread implements Runnable {
    private final ElevatorInput elevatorInput;
    private final RequestQueue waitQueue;

    public InputThread(ElevatorInput elevatorInput, RequestQueue waitQueue) {
        this.elevatorInput = elevatorInput;
        this.waitQueue = waitQueue;
    }

    @Override
    public void run() {
        while (true) {
            PersonRequest request = elevatorInput.nextPersonRequest();
            if (request == null) {
                waitQueue.setEnd(true);
                break;
            } else {
                waitQueue.add(request);
            }
        }
        try {
            elevatorInput.close();
        } catch (IOException e) {
            e.printStackTrace();
        }

    }
}