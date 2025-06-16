import com.oocourse.spec3.main.Person;
import com.oocourse.spec3.main.RedEnvelopeMessage;
import com.oocourse.spec3.main.Tag;

public class MyRedEnvelopeMessage extends MyMessage implements RedEnvelopeMessage {
    private final int money;

    public MyRedEnvelopeMessage(int messageId, int luckyMoney, Person messagePerson1,
                                Person messagePerson2) {
        super(messageId, 5 * luckyMoney, messagePerson1, messagePerson2);
        money = luckyMoney;
    }

    public MyRedEnvelopeMessage(int messageId, int luckyMoney, Person messagePerson1,
                                Tag messageTag) {
        super(messageId, 5 * luckyMoney, messagePerson1, messageTag);
        money = luckyMoney;
    }

    @Override
    public int getMoney() {
        return money;
    }
}
