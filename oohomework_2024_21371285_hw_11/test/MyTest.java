import com.oocourse.spec3.exceptions.*;
import com.oocourse.spec3.main.EmojiMessage;
import com.oocourse.spec3.main.Message;
import org.junit.Test;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class MyTest {
    @Test
    public void testDeleteColdEmoji() {
        MyNetwork network = new MyNetwork();
        MyNetwork copy = new MyNetwork();
        Random random = new Random(20240510L);

        MyPerson[] peopleNetwork = new MyPerson[20];
        MyPerson[] peopleCopy = new MyPerson[20];
        MyTag[] tagsNetwork = new MyTag[100];
        MyTag[] tagsCopy = new MyTag[100];

        for (int i = 0; i < 20; i++) {
            MyPerson pr1 = new MyPerson(i, String.valueOf(i), 18);
            MyPerson pr2 = new MyPerson(i, String.valueOf(i), 18);
            try {
                network.addPerson(pr1);
                copy.addPerson(pr2);
                peopleNetwork[i] = pr1;
                peopleCopy[i] = pr2;
            } catch (EqualPersonIdException e) {
                e.print();
            }
        }

        for (int i = 0; i < 20; i++) {
            for (int j = i + 1; j < 20; j++) {
                try {
                    network.addRelation(i, j, 200);
                    copy.addRelation(i, j, 200);
                } catch (PersonIdNotFoundException | EqualRelationException e) {
                    e.printStackTrace();
                }
            }
        }

        for (int i = 0; i < 100; i++) {
            int personId = random.nextInt(20);
            MyTag tag1 = new MyTag(i);
            MyTag tag2 = new MyTag(i);
            try {
                network.addTag(personId, tag1);
                copy.addTag(personId, tag2);

                tagsNetwork[i] = tag1;
                tagsCopy[i] = tag2;

                int j = 10;
                while (j-- > 0) {
                    int p1Id = random.nextInt(20);
                    network.addPersonToTag(p1Id, personId, i);
                    copy.addPersonToTag(p1Id, personId, i);
                }
            } catch (Exception e) {
                e.printStackTrace();
            }
        }

        for (int i = 0; i < 10; i++) {
            try {
                network.storeEmojiId(i);
                copy.storeEmojiId(i);
            } catch (EqualEmojiIdException e) {
                e.print();
            }
        }

        System.out.println("BEGIN ADD MESSAGE");
        HashSet<Integer> mesIds = new HashSet<>();

        for (int i = 0; i < 200; i++) {
            int type = random.nextInt(2);
            int choice = random.nextInt(10);
            int p1_id = random.nextInt(20);
            int p2_id = random.nextInt(20);
            int tag_id = random.nextInt(100);
            int mesId = random.nextInt();
            int value = random.nextInt(5);
            Message mes1;
            Message mes2;
            if (type == 0) {
                switch (choice) {
                    case 0:
                        mes1 = new MyMessage(mesId, value, peopleNetwork[p1_id], peopleNetwork[p2_id]);
                        mes2 = new MyMessage(mesId, value, peopleCopy[p1_id], peopleCopy[p2_id]);
                        break;
                    case 1:
                        mes1 = new MyNoticeMessage(mesId, String.valueOf(value), peopleNetwork[p1_id], peopleNetwork[p2_id]);
                        mes2 = new MyNoticeMessage(mesId, String.valueOf(value), peopleCopy[p1_id], peopleCopy[p2_id]);
                        break;
                    case 2:
                        mes1 = new MyRedEnvelopeMessage(mesId, value, peopleNetwork[p1_id], peopleNetwork[p2_id]);
                        mes2 = new MyRedEnvelopeMessage(mesId, value, peopleCopy[p1_id], peopleCopy[p2_id]);
                        break;
                    default:
                        mes1 = new MyEmojiMessage(mesId, value, peopleNetwork[p1_id], peopleNetwork[p2_id]);
                        mes2 = new MyEmojiMessage(mesId, value, peopleCopy[p1_id], peopleCopy[p2_id]);
                        break;
                }
            } else {
                switch (choice) {
                    case 0:
                        mes1 = new MyMessage(mesId, value, peopleNetwork[p1_id], tagsNetwork[tag_id]);
                        mes2 = new MyMessage(mesId, value, peopleCopy[p1_id], tagsCopy[tag_id]);
                        break;
                    case 1:
                        mes1 = new MyNoticeMessage(mesId, String.valueOf(value), peopleNetwork[p1_id], tagsNetwork[tag_id]);
                        mes2 = new MyNoticeMessage(mesId, String.valueOf(value), peopleCopy[p1_id], tagsCopy[tag_id]);
                        break;
                    case 2:
                        mes1 = new MyRedEnvelopeMessage(mesId, value, peopleNetwork[p1_id], tagsNetwork[tag_id]);
                        mes2 = new MyRedEnvelopeMessage(mesId, value, peopleCopy[p1_id], tagsCopy[tag_id]);
                        break;
                    default:
                        mes1 = new MyEmojiMessage(mesId, value, peopleNetwork[p1_id], tagsNetwork[tag_id]);
                        mes2 = new MyEmojiMessage(mesId, value, peopleCopy[p1_id], tagsCopy[tag_id]);
                        break;
                }
            }
            try {
                network.addMessage(mes1);
                copy.addMessage(mes2);
                mesIds.add(mesId);
            } catch (EqualMessageIdException | EmojiIdNotFoundException | EqualPersonIdException e) {
                e.printStackTrace();
            }
        }

        for (Integer mesId: mesIds) {
            if (random.nextBoolean()) {
                try {
                    network.sendMessage(mesId);
                    copy.sendMessage(mesId);
                } catch (RelationNotFoundException | MessageIdNotFoundException | TagIdNotFoundException e) {
                    e.printStackTrace();
                }
            }
        }

        Message[] messCopy = copy.getMessages();
        int messlen = messCopy.length;
        int[] emojiIdListCopy = copy.getEmojiIdList();
        int[] emojiHeatListCopy = copy.getEmojiHeatList();
        int emojiLen = emojiHeatListCopy.length;
        Message[] mess;
        int[] emojiIdList;
        int[] emojiHeatList;
        for (int i = 0; i < 20; i++) {
            mess = network.getMessages();
            emojiIdList = network.getEmojiIdList();
            emojiHeatList = network.getEmojiHeatList();
            HashSet<Message> tmp0 = new HashSet<>(Arrays.asList(mess));
            assertEquals(tmp0.size(), mess.length);
            assertEquals(messlen, mess.length);
            Set<Integer> tmp = IntStream.of(emojiIdList).boxed().collect(Collectors.toSet());
            assertEquals(tmp.size(), emojiIdList.length);
            assertEquals(emojiHeatList.length, emojiIdList.length);
            assertEquals(emojiLen, emojiIdList.length);
            for (Message mes : tmp0) {
                if (mes instanceof EmojiMessage) {
                    int emojiId = ((EmojiMessage) mes).getEmojiId();
                    assertTrue(tmp.contains(emojiId));
                }
            }

            int cnt = 0;

            for (int j = 0; j < emojiLen; j++) {
                for (int k = 0; k < emojiIdList.length; k++) {
                    if (emojiIdListCopy[j] == emojiIdList[k]) {
                        assertEquals(emojiHeatListCopy[j], emojiHeatList[k]);
                        cnt++;
                        break;
                    }
                }
            }

            assertEquals(emojiIdList.length, cnt);

            int ret = network.deleteColdEmoji(i);

            for (int j = 0; j < emojiHeatListCopy.length; j++) {
                if (emojiHeatListCopy[j] < i) {
                    emojiHeatListCopy[j] = -1;
                    for (int k = 0; k < messCopy.length; k++) {
                        Message mes = messCopy[k];
                        if (mes instanceof EmojiMessage) {
                            if (((EmojiMessage) mes).getEmojiId() == emojiIdListCopy[j]) {
                                messCopy[k] = null;
                            }
                        }
                    }
                }
            }
            int slow = 0;
            for (int j = 0; j < messlen; j++) {
                if (messCopy[j] != null) {
                    messCopy[slow++] = messCopy[j];
                }
            }
            messlen = slow;
            slow = 0;
            for (int j = 0; j < emojiLen; j++) {
                if (emojiHeatListCopy[j] != -1) {
                    emojiHeatListCopy[slow] = emojiHeatListCopy[j];
                    emojiIdListCopy[slow++] = emojiIdListCopy[j];
                }
            }
            emojiLen = slow;

            assertEquals(ret, emojiLen);
        }
    }
}
