import com.oocourse.elevator3.ElevatorInput;
import com.oocourse.elevator3.TimableOutput;
import entities.Elevator;
import entities.RequestQueue;
import entities.Scheduler;

public class MainClass {
    public static void main(String[] args) {
        TimableOutput.initStartTimestamp();
        ElevatorInput elevatorInput = new ElevatorInput(System.in);
        RequestQueue waitQueue = new RequestQueue();
        Dispatcher dispatcher = new Dispatcher(waitQueue);
        InputThread inputThread = new InputThread(elevatorInput, waitQueue, dispatcher);
        for (int i = 1; i <= 6; i++) {
            Elevator elevator = new Elevator(String.valueOf(i));
            Scheduler scheduler = new Scheduler(elevator);
            ElevatorThread et = new ElevatorThread(elevator, scheduler, waitQueue, dispatcher);
            dispatcher.add(i, scheduler);
            inputThread.add(i, scheduler);
            new Thread(et, "Elevator " + i).start();
        }
        Thread tmp = new Thread(dispatcher, "Dispatcher");
        tmp.start();
        new Thread(inputThread, "Input").start();
    }
}