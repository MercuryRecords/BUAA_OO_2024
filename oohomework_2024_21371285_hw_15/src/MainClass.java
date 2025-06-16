import com.oocourse.library3.annotation.Trigger;

public class MainClass {
    @Trigger(from = "InitState", to = "S1")
    @Trigger(from = "S1", to = "S1")
    public static void main(String[] args) {
        Controller controller = new Controller();
        controller.start();
    }
}
