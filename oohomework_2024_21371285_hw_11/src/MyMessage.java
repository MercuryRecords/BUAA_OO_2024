import com.oocourse.spec3.main.Message;
import com.oocourse.spec3.main.Person;
import com.oocourse.spec3.main.Tag;

public class MyMessage implements Message {
    private final int type;
    private final int id;
    private final int socialValue;
    private final Person person1;
    private final Person person2;
    private final Tag tag;

    public MyMessage(int messageId, int messageSocialValue, Person messagePerson1,
                     Person messagePerson2) {
        type = 0;
        tag = null;
        id = messageId;
        socialValue = messageSocialValue;
        person1 = messagePerson1;
        person2 = messagePerson2;
    }

    public MyMessage(int messageId, int messageSocialValue, Person messagePerson1,
                     Tag messageTag) {
        type = 1;
        tag = messageTag;
        id = messageId;
        socialValue = messageSocialValue;
        person1 = messagePerson1;
        person2 = null;
    }

    @Override
    public int getType() {
        return type;
    }

    @Override
    public int getId() {
        return id;
    }

    @Override
    public int getSocialValue() {
        return socialValue;
    }

    @Override
    public Person getPerson1() {
        return person1;
    }

    /* requires \result != null */
    @Override
    public Person getPerson2() {
        return person2;
    }

    /* requires \result != null */
    @Override
    public Tag getTag() {
        return tag;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj instanceof Message) {
            return ((Message) obj).getId() == id;
        }
        return false;
    }
}
