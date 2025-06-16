import com.oocourse.elevator2.ElevatorInput;
import com.oocourse.elevator2.TimableOutput;
import entities.Elevator;
import entities.RequestQueue;
import entities.Scheduler;

public class MainClass {
    public static void main(String[] args) {
        TimableOutput.initStartTimestamp();
        ElevatorInput elevatorInput = new ElevatorInput(System.in);
        RequestQueue waitQueue = new RequestQueue();
        InputThread inputThread = new InputThread(elevatorInput, waitQueue);
        Dispatcher dispatcher = new Dispatcher(waitQueue);
        for (int i = 1; i <= 6; i++) {
            Elevator elevator = new Elevator(i);
            Scheduler scheduler = new Scheduler(elevator);
            ElevatorThread et = new ElevatorThread(elevator, scheduler, waitQueue);
            dispatcher.add(i, scheduler);
            inputThread.add(i, scheduler);
            new Thread(et, "entitys.Elevator " + i).start();
        }
        Thread tmp = new Thread(dispatcher, "Dispatcher");
        tmp.start();
        new Thread(inputThread, "Input").start();
    }
}