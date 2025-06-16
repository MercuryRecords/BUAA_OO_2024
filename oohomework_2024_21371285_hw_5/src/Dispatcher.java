import com.oocourse.elevator1.PersonRequest;
import java.util.HashMap;

public class Dispatcher implements Runnable {

    private final RequestQueue waitQueue;
    private final HashMap<Integer, Scheduler> queues = new HashMap<>();
    
    public Dispatcher(RequestQueue waitQueue) {
        this.waitQueue = waitQueue;
    }

    @Override
    public void run() {
        while (true) {
            PersonRequest request = waitQueue.take();
            if (request == null) {
                for (Scheduler scheduler: queues.values()) {
                    scheduler.setEnd();
                }
                break;
            } else {
                Scheduler toPut = queues.get(request.getElevatorId());
                toPut.addRequest(request);
            }
        }
    }

    public void add(int i, Scheduler scheduler) {
        this.queues.put(i, scheduler);
    }
}
