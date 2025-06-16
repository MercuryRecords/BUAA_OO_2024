import com.oocourse.spec3.main.EmojiMessage;
import com.oocourse.spec3.main.Person;
import com.oocourse.spec3.main.Tag;

public class MyEmojiMessage extends MyMessage implements EmojiMessage {
    private final int emojiId;

    public MyEmojiMessage(int messageId, int emojiNumber, Person messagePerson1,
                          Person messagePerson2) {
        super(messageId, emojiNumber, messagePerson1, messagePerson2);
        emojiId = emojiNumber;
    }

    public MyEmojiMessage(int messageId, int emojiNumber, Person messagePerson1,
                          Tag messageTag) {
        super(messageId, emojiNumber, messagePerson1, messageTag);
        emojiId = emojiNumber;
    }

    @Override
    public int getEmojiId() {
        return emojiId;
    }
}
