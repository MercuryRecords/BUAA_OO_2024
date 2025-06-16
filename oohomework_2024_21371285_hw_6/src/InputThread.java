import com.oocourse.elevator2.ElevatorInput;
import com.oocourse.elevator2.PersonRequest;
import com.oocourse.elevator2.Request;
import com.oocourse.elevator2.ResetRequest;
import entities.RequestQueue;
import entities.Scheduler;

import java.io.IOException;
import java.util.HashMap;

class InputThread implements Runnable {
    private final ElevatorInput elevatorInput;
    private final RequestQueue requestQueue;
    private final HashMap<Integer, Scheduler> queues = new HashMap<>();

    public InputThread(ElevatorInput elevatorInput, RequestQueue requestQueue) {
        this.elevatorInput = elevatorInput;
        this.requestQueue = requestQueue;
    }

    @Override
    public void run() {
        while (true) {
            Request request = elevatorInput.nextRequest();
            if (request == null) {
                requestQueue.setEnd(true);
                break;
            } else {
                if (request instanceof PersonRequest) {
                    requestQueue.add((PersonRequest) request);
                } else if (request instanceof ResetRequest) {
                    requestQueue.addReset();
                    ResetRequest resetRequest = (ResetRequest) request;
                    Scheduler tmpScheduler = queues.get(resetRequest.getElevatorId());
                    synchronized (tmpScheduler) {
                        tmpScheduler.preset(resetRequest.getCapacity(), resetRequest.getSpeed());
                    }
                }
            }
        }
        try {
            elevatorInput.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    public void add(int i, Scheduler scheduler) {
        this.queues.put(i, scheduler);
    }
}