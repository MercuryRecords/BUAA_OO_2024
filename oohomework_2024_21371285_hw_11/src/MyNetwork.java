import com.oocourse.spec3.exceptions.AcquaintanceNotFoundException;
import com.oocourse.spec3.exceptions.EmojiIdNotFoundException;
import com.oocourse.spec3.exceptions.EqualEmojiIdException;
import com.oocourse.spec3.exceptions.EqualMessageIdException;
import com.oocourse.spec3.exceptions.EqualPersonIdException;
import com.oocourse.spec3.exceptions.EqualRelationException;
import com.oocourse.spec3.exceptions.EqualTagIdException;
import com.oocourse.spec3.exceptions.MessageIdNotFoundException;
import com.oocourse.spec3.exceptions.PathNotFoundException;
import com.oocourse.spec3.exceptions.PersonIdNotFoundException;
import com.oocourse.spec3.exceptions.RelationNotFoundException;
import com.oocourse.spec3.exceptions.TagIdNotFoundException;
import com.oocourse.spec3.main.EmojiMessage;
import com.oocourse.spec3.main.Message;
import com.oocourse.spec3.main.Network;
import com.oocourse.spec3.main.Person;
import com.oocourse.spec3.main.RedEnvelopeMessage;
import com.oocourse.spec3.main.Tag;
import exception.MyAcquaintanceNotFoundException;
import exception.MyEmojiIdNotFoundException;
import exception.MyEqualEmojiIdException;
import exception.MyEqualMessageIdException;
import exception.MyEqualPersonIdException;
import exception.MyEqualRelationException;
import exception.MyEqualTagIdException;
import exception.MyMessageIdNotFoundException;
import exception.MyPathNotFoundException;
import exception.MyPersonIdNotFoundException;
import exception.MyRelationNotFoundException;
import exception.MyTagIdNotFoundException;

import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class MyNetwork implements Network {
    private final HashMap<Integer, Person> persons = new HashMap<>();
    private final DisjointSet pa = new DisjointSet(persons);
    private final HashMap<Integer, HashMap<Integer, HashSet<Tag>>> followerToTags = new HashMap<>();
    private int tripleSum = 0;
    private int blockSum = 0;
    private int coupleSum = 0;
    private boolean coupleCached = false;
    private final HashMap<Integer, Message> messages = new HashMap<>();
    private final HashMap<Integer, Integer> emojiIdToHeat = new HashMap<>();
    private final HashMap<Integer, HashSet<Integer>> emojiIdToMess = new HashMap<>();

    public MyNetwork() {}

    @Override
    public boolean containsMessage(int id) { return messages.containsKey(id); }

    @Override
    public void addMessage(Message message) throws EqualMessageIdException,
            EmojiIdNotFoundException, EqualPersonIdException {
        if (messages.containsKey(message.getId())) {
            throw new MyEqualMessageIdException(message.getId());
        } else if (message instanceof EmojiMessage &&
            !containsEmojiId(((EmojiMessage) message).getEmojiId())) {
            throw new MyEmojiIdNotFoundException(((EmojiMessage) message).getEmojiId());
        } else if (message.getType() == 0 && message.getPerson1().equals(message.getPerson2())) {
            throw new MyEqualPersonIdException(message.getPerson1().getId());
        }
        messages.put(message.getId(), message);
        if (message instanceof EmojiMessage) {
            emojiIdToMess.get(((EmojiMessage) message).getEmojiId()).add(message.getId());
        }
    }

    @Override
    public Message getMessage(int id) { return messages.getOrDefault(id, null); }

    @Override
    public void sendMessage(int id) throws RelationNotFoundException, MessageIdNotFoundException,
            TagIdNotFoundException {
        if (!messages.containsKey(id)) { throw new MyMessageIdNotFoundException(id); }
        Message mes = messages.get(id);
        Person p1 = mes.getPerson1();
        if (mes.getType() == 0) {
            if (!mes.getPerson1().isLinked(messages.get(id).getPerson2())) {
                throw new MyRelationNotFoundException(p1.getId(), mes.getPerson2().getId());
            }
            Person p2 = mes.getPerson2();
            p1.addSocialValue(mes.getSocialValue());
            p2.addSocialValue(mes.getSocialValue());
            if (mes instanceof RedEnvelopeMessage) {
                p1.addMoney(-((RedEnvelopeMessage) mes).getMoney());
                p2.addMoney(((RedEnvelopeMessage) mes).getMoney());
            } else if (mes instanceof EmojiMessage) {
                int emojiId = ((EmojiMessage) mes).getEmojiId();
                emojiIdToHeat.replace(emojiId, emojiIdToHeat.get(emojiId) + 1);
            }
            ((MyPerson) p2).addMessage(mes);
        } else {
            MyTag tag = (MyTag) mes.getTag();
            if (!p1.containsTag(tag.getId())) { throw new MyTagIdNotFoundException(tag.getId()); }
            p1.addSocialValue(mes.getSocialValue());
            for (Person pr: (tag.getPersons())) {
                pr.addSocialValue(mes.getSocialValue());
            }
            if (mes instanceof RedEnvelopeMessage && tag.getSize() > 0) {
                int moneyPer = ((RedEnvelopeMessage) mes).getMoney() / tag.getSize();
                p1.addMoney(- moneyPer * tag.getSize());
                for (Person pr: tag.getPersons()) {
                    pr.addMoney(moneyPer);
                }
            } else if (mes instanceof EmojiMessage) {
                int emojiId = ((EmojiMessage) mes).getEmojiId();
                emojiIdToHeat.replace(emojiId, emojiIdToHeat.get(emojiId) + 1);
            }
        }
        messages.remove(id);
        if (mes instanceof EmojiMessage) {
            emojiIdToMess.get(((EmojiMessage) mes).getEmojiId()).remove(mes.getId());
        }
    }

    @Override
    public int querySocialValue(int id) throws PersonIdNotFoundException {
        findPersonIdInPersons(id);
        return persons.get(id).getSocialValue();
    }

    @Override
    public List<Message> queryReceivedMessages(int id) throws PersonIdNotFoundException {
        findPersonIdInPersons(id);
        return persons.get(id).getReceivedMessages();
    }

    @Override
    public boolean containsEmojiId(int id) { return emojiIdToHeat.containsKey(id); }

    @Override
    public void storeEmojiId(int id) throws EqualEmojiIdException {
        if (emojiIdToHeat.containsKey(id)) { throw new MyEqualEmojiIdException(id); }
        emojiIdToHeat.put(id, 0);
        emojiIdToMess.put(id, new HashSet<>());
    }

    @Override
    public int queryMoney(int id) throws PersonIdNotFoundException {
        findPersonIdInPersons(id);
        return persons.get(id).getMoney();
    }

    @Override
    public int queryPopularity(int id) throws EmojiIdNotFoundException {
        if (!emojiIdToHeat.containsKey(id)) { throw new MyEmojiIdNotFoundException(id); }
        return emojiIdToHeat.get(id);
    }

    @Override
    public int deleteColdEmoji(int limit) {
        Iterator<Map.Entry<Integer, Integer>> it = emojiIdToHeat.entrySet().iterator();
        while (it.hasNext()) {
            Map.Entry<Integer, Integer> entry = it.next();
            if (entry.getValue() < limit) {
                it.remove();
                HashSet<Integer> mess = emojiIdToMess.get(entry.getKey());
                for (Integer id: mess) {
                    messages.remove(id);
                }
                emojiIdToMess.remove(entry.getKey());
            }
        }
        return emojiIdToMess.size();
    }

    @Override
    public void clearNotices(int personId) throws PersonIdNotFoundException {
        findPersonIdInPersons(personId);
        ((MyPerson) persons.get(personId)).clearNotices();
    }

    @Override
    public boolean containsPerson(int id) { return persons.containsKey(id); }

    private void findPersonId(int id1, int id2) throws MyPersonIdNotFoundException {
        if (!persons.containsKey(id1)) { throw new MyPersonIdNotFoundException(id1); }
        if (!persons.containsKey(id2)) { throw new MyPersonIdNotFoundException(id2); }
    }

    private void findPersonIdInPersons(int id) throws MyPersonIdNotFoundException {
        if (!persons.containsKey(id)) { throw new MyPersonIdNotFoundException(id); }
    }

    private void findRelation(int id1, int id2) throws MyRelationNotFoundException {
        if (!getPerson(id1).isLinked(getPerson(id2))) {
            throw new MyRelationNotFoundException(id1, id2);
        }
    }

    private void findTagId(int personId, int tagId) throws MyTagIdNotFoundException {
        if (!persons.get(personId).containsTag(tagId)) {
            throw new MyTagIdNotFoundException(tagId);
        }
    }

    @Override
    public Person getPerson(int id) { return persons.getOrDefault(id, null); }

    @Override
    public void addPerson(Person person) throws EqualPersonIdException {
        int id = person.getId();
        if (persons.containsKey(id)) { throw new MyEqualPersonIdException(id); }
        persons.put(id, person);
        pa.add(id);
        followerToTags.put(id, new HashMap<>());
        blockSum++;
    }

    @Override
    public void addRelation(int id1, int id2, int value) throws
            PersonIdNotFoundException, EqualRelationException {
        findPersonId(id1, id2);
        if (getPerson(id1).isLinked(getPerson(id2))) {
            throw new MyEqualRelationException(id1, id2);
        }
        MyPerson p1 = (MyPerson) getPerson(id1);
        MyPerson p2 = (MyPerson) getPerson(id2);
        if (p1.getAcquaintance().isEmpty() || p2.getAcquaintance().isEmpty()) {
            coupleCached = false;
        } else if ((value >= p1.queryValue(persons.get(p1.getBest()))) ||
                   (value >= p2.queryValue(persons.get(p2.getBest())))) {
            coupleCached = false;
        }
        if (pa.find(id1) != pa.find(id2)) { blockSum--; }
        p1.link(p2, value);
        p2.link(p1, value);
        Set<Integer> interSet = new HashSet<>(p1.getAcquaintance());
        interSet.retainAll(p2.getAcquaintance());
        tripleSum += interSet.size();
        pa.union(id1, id2);
        updateRelationValueToTag(id1, id2, 0, 2 * value);
    }

    @Override
    public void modifyRelation(int id1, int id2, int value) throws
            PersonIdNotFoundException, EqualPersonIdException, RelationNotFoundException {
        findPersonId(id1, id2);
        if (id1 == id2) { throw new MyEqualPersonIdException(id1); }
        findRelation(id1, id2);
        MyPerson p1 = (MyPerson) getPerson(id1);
        MyPerson p2 = (MyPerson) getPerson(id2);
        int oldValue = p1.queryValue(p2);
        int newValue = oldValue + value;
        int oldBestie1 = p1.getBest();
        int oldBestie2 = p2.getBest();
        if (newValue <= 0) {
            p1.unlink(p2);
            p2.unlink(p1);
            Set<Integer> interSet = new HashSet<>(p1.getAcquaintance());
            interSet.retainAll(p2.getAcquaintance());
            tripleSum -= interSet.size();
            pa.unlink(id1, id2);
            if (pa.find(id1) != pa.find(id2)) {
                blockSum++;
            }
            cleanTags(id1, id2);
            cleanTags(id2, id1);
        } else {
            p1.updateValue(p2, newValue);
            p2.updateValue(p1, newValue);
        }
        updateRelationValueToTag(id1, id2, 2 * oldValue, 2 * newValue);
        if (p1.getAcquaintance().isEmpty() || p2.getAcquaintance().isEmpty()) {
            coupleCached = false;
        } else if (oldBestie1 != p1.getBest() || oldBestie2 != p2.getBest()) {
            coupleCached = false;
        }
    }

    private void cleanTags(int id1, int id2) {
        if (followerToTags.get(id1).containsKey(id2)) {
            for (Tag tag: followerToTags.get(id1).get(id2)) {
                tag.delPerson(persons.get(id1));
            }
            followerToTags.get(id1).remove(id2);
        }
    }

    private void updateRelationValueToTag(int id1, int id2, int oldVal, int newVal) {
        for (HashSet<Tag> tags: followerToTags.get(id1).values()) {
            for (Tag tag: tags) {
                if (tag.hasPerson(persons.get(id2))) { ((MyTag) tag).updateValue(oldVal, newVal); }
            }
        }
    }

    @Override
    public int queryValue(int id1, int id2) throws
            PersonIdNotFoundException, RelationNotFoundException {
        findPersonId(id1, id2);
        findRelation(id1, id2);
        return getPerson(id1).queryValue(getPerson(id2));
    }

    @Override
    public boolean isCircle(int id1, int id2) throws PersonIdNotFoundException {
        findPersonId(id1, id2);
        return pa.find(id1) == pa.find(id2);
    }

    @Override
    public int queryBlockSum() {
        return blockSum;
    }

    @Override
    public int queryTripleSum() {
        return tripleSum;
    }

    @Override
    public void addTag(int personId, Tag tag) throws
            PersonIdNotFoundException, EqualTagIdException {
        findPersonIdInPersons(personId);
        Person person = persons.get(personId);
        int tagId = tag.getId();
        if (person.containsTag(tagId)) { throw new MyEqualTagIdException(tagId); }
        person.addTag(tag);
    }

    @Override
    public void addPersonToTag(int personId1, int personId2, int tagId) throws
            PersonIdNotFoundException, RelationNotFoundException, TagIdNotFoundException,
            EqualPersonIdException {
        findPersonId(personId1, personId2);
        if (personId1 == personId2) { throw new MyEqualPersonIdException(personId1); }
        findRelation(personId2, personId1);
        findTagId(personId2, tagId);
        Tag tag = persons.get(personId2).getTag(tagId);
        if (tag.hasPerson(persons.get(personId1))) {
            throw new MyEqualPersonIdException(personId1);
        } else if (tag.getSize() <= 1111) {
            tag.addPerson(persons.get(personId1));
            HashMap<Integer, HashSet<Tag>> map = followerToTags.get(personId1);
            if (map.containsKey(personId2)) { map.get(personId2).add(tag); } else {
                HashSet<Tag> tags = new HashSet<>();
                tags.add(tag);
                map.put(personId2, tags);
            }
        }
    }

    @Override
    public int queryTagValueSum(int personId, int tagId) throws
            PersonIdNotFoundException, TagIdNotFoundException {
        findPersonIdInPersons(personId);
        findTagId(personId, tagId);
        return persons.get(personId).getTag(tagId).getValueSum();
    }

    @Override
    public int queryTagAgeVar(int personId, int tagId) throws
            PersonIdNotFoundException, TagIdNotFoundException {
        findPersonIdInPersons(personId);
        findTagId(personId, tagId);
        return persons.get(personId).getTag(tagId).getAgeVar();
    }

    @Override
    public void delPersonFromTag(int personId1, int personId2, int tagId) throws
            PersonIdNotFoundException, TagIdNotFoundException {
        findPersonId(personId1, personId2);
        findTagId(personId2, tagId);
        Tag tag = persons.get(personId2).getTag(tagId);
        Person person1 = persons.get(personId1);
        if (!tag.hasPerson(person1)) { throw new MyPersonIdNotFoundException(personId1); }
        tag.delPerson(person1);
        HashMap<Integer, HashSet<Tag>> map = followerToTags.get(personId1);
        HashSet<Tag> tags = map.get(personId2);
        tags.remove(tag);
        if (tags.isEmpty()) { map.remove(personId2); }
    }

    @Override
    public void delTag(int personId, int tagId) throws
            PersonIdNotFoundException, TagIdNotFoundException {
        findPersonIdInPersons(personId);
        findTagId(personId, tagId);
        for (HashMap<Integer, HashSet<Tag>> map: followerToTags.values()) {
            if (map.containsKey(personId)) {
                map.get(personId).remove(persons.get(personId).getTag(tagId));
            }
        }
        persons.get(personId).delTag(tagId);
    }

    @Override
    public int queryBestAcquaintance(int id) throws
            PersonIdNotFoundException, AcquaintanceNotFoundException {
        findPersonIdInPersons(id);
        if (((MyPerson) persons.get(id)).getAcquaintance().isEmpty()) {
            throw new MyAcquaintanceNotFoundException(id);
        }
        return ((MyPerson) persons.get(id)).getBest();
    }

    @Override
    public int queryCoupleSum() {
        if (!coupleCached) {
            coupleSum = 0;
            for (Map.Entry<Integer, Person> entry : persons.entrySet()) {
                Integer id = entry.getKey();
                Person value = entry.getValue();
                if (!((MyPerson) value).getAcquaintance().isEmpty()) {
                    int bestie = ((MyPerson) value).getBest();
                    if (bestie < id && ((MyPerson) persons.get(bestie)).getBest() == id) {
                        coupleSum++;
                    }
                }
            }
            coupleCached = true;
        }
        return coupleSum;
    }

    @Override
    public int queryShortestPath(int id1, int id2) throws
            PersonIdNotFoundException, PathNotFoundException {
        findPersonId(id1, id2);
        if (pa.find(id1) != pa.find(id2)) { throw new MyPathNotFoundException(id1, id2); }
        else if (id1 == id2) { return 0; }
        int dis = -1;
        ArrayDeque<Integer> queue1 = new ArrayDeque<>();
        queue1.add(id1);
        ArrayDeque<Integer> queue2 = new ArrayDeque<>();
        queue2.add(id2);
        Set<Integer> visited1 = new HashSet<>();
        visited1.add(id1);
        Set<Integer> visited2 = new HashSet<>();
        visited2.add(id2);
        while (!queue1.isEmpty() && !queue2.isEmpty()) {
            dis++;
            if (queue1.size() <= queue2.size()) {
                if (updateBiBfs(queue1, visited1, visited2)) { break; }
            } else { if (updateBiBfs(queue2, visited2, visited1)) { break; } }
        }
        return dis;
    }

    private boolean updateBiBfs(ArrayDeque<Integer> q, Set<Integer> visited, Set<Integer> other) {
        ArrayDeque<Integer> thisFloor = new ArrayDeque<>(q);
        while (!thisFloor.isEmpty()) {
            Integer curr = q.pollFirst();
            thisFloor.removeFirst();
            for (int ac : ((MyPerson) persons.get(curr)).getAcquaintance()) {
                if (visited.contains(ac)) { continue; }
                if (other.contains(ac)) { return true; }
                visited.add(ac);
                q.add(ac);
            }
        }
        return false;
    }

    public Person[] getPersons() {
        Person[] ret = new Person[persons.size()];
        int i = 0;
        for (Person person: persons.values()) { ret[i++] = person; }
        return ret;
    }

    public Message[] getMessages() { return messages.values().toArray(new Message[0]); }

    public int[] getEmojiIdList() {
        return emojiIdToHeat.keySet().stream().mapToInt(Integer::intValue).toArray(); }

    public int[] getEmojiHeatList() {
        return emojiIdToHeat.values().stream().mapToInt(Integer::intValue).toArray(); }
}
