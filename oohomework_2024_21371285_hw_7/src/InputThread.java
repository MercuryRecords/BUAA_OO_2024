import com.oocourse.elevator3.ElevatorInput;
import com.oocourse.elevator3.PersonRequest;
import com.oocourse.elevator3.Request;
import com.oocourse.elevator3.NormalResetRequest;
import com.oocourse.elevator3.DoubleCarResetRequest;
import entities.RequestQueue;
import entities.Scheduler;

import java.io.IOException;
import java.util.HashMap;

class InputThread implements Runnable {
    private final ElevatorInput elevatorInput;
    private final RequestQueue requestQueue;
    private final Dispatcher dispatcher;
    private final HashMap<Integer, Scheduler> queues = new HashMap<>();

    public InputThread(ElevatorInput elevatorInput, RequestQueue requestQueue, Dispatcher disp) {
        this.elevatorInput = elevatorInput;
        this.requestQueue = requestQueue;
        this.dispatcher = disp;
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
                } else if (request instanceof NormalResetRequest) {
                    requestQueue.addReset();
                    NormalResetRequest rsRequest = (NormalResetRequest) request;
                    Scheduler tmpScheduler = queues.get(rsRequest.getElevatorId());
                    synchronized (tmpScheduler) {
                        tmpScheduler.preset(rsRequest.getCapacity(), rsRequest.getSpeed(), true);
                    }
                } else if (request instanceof DoubleCarResetRequest) {
                    requestQueue.addReset();
                    DoubleCarResetRequest dcRequest = (DoubleCarResetRequest) request;
                    Scheduler tmpScheduler = queues.get(dcRequest.getElevatorId());
                    synchronized (tmpScheduler) {
                        tmpScheduler.preset(dcRequest.getCapacity(), dcRequest.getSpeed(), false);
                        dispatcher.preReplace(dcRequest.getElevatorId(), dcRequest);
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