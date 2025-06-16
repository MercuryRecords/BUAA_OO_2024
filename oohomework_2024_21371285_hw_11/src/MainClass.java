import com.oocourse.spec3.main.Runner;

public class MainClass {
    public static void main(String[] args) throws Exception {
        Runner runner = new Runner(MyPerson.class, MyNetwork.class, MyTag.class, MyMessage.class,
                MyEmojiMessage.class, MyNoticeMessage.class, MyRedEnvelopeMessage.class);
        runner.run();
    }
}
