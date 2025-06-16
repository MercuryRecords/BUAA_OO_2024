import com.oocourse.elevator1.ElevatorInput;
import com.oocourse.elevator1.TimableOutput;

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
            ElevatorThread et = new ElevatorThread(elevator, scheduler);
            dispatcher.add(i, scheduler);
            new Thread(et, "Elevator " + i).start();
        }
        new Thread(dispatcher, "Dispatcher").start();
        new Thread(inputThread, "Input").start();
    }
}


/*
1. 考虑性能分，LOOK > ALS √
2. 电梯和电梯线程分离 √
3. 量子电梯 √？
4. 影子电梯？
5.
 */