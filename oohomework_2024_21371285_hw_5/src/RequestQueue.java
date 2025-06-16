import com.oocourse.elevator1.PersonRequest;
import java.util.ArrayList;

public class RequestQueue {
    private final ArrayList<PersonRequest> requests;
    private boolean end;

    public RequestQueue() {
        this.requests = new ArrayList<>();
        this.end = false;
    }

    public synchronized void add(PersonRequest pr) {
        this.requests.add(pr);
        notify();
    }

    public synchronized PersonRequest take() {
        if (requests.isEmpty() && !this.end) {
            try {
                wait();
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }

        if (requests.isEmpty()) {
            return null;
        }
        PersonRequest pr = requests.get(0);
        requests.remove(0);
        notify();
        return pr;
    }

    public synchronized void setEnd(boolean flag) {
        this.end = flag;
        notify();
    }

}
