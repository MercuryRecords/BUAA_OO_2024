import com.oocourse.spec3.main.Message;
import com.oocourse.spec3.main.NoticeMessage;
import com.oocourse.spec3.main.Person;
import com.oocourse.spec3.main.Tag;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;

public class MyPerson implements Person {
    private final int id;
    private final String name;
    private final int age;
    private final TreeSet<Person> acquaintance = new TreeSet<>(new Comparator<Person>() {
        @Override
        public int compare(Person p1, Person p2) {
            int id1 = p1.getId();
            int id2 = p2.getId();
            int cmp = Integer.compare(idToValue.getOrDefault(id2, Integer.MAX_VALUE),
                    idToValue.getOrDefault(id1, Integer.MAX_VALUE));
            if (cmp == 0) {
                return Integer.compare(id1, id2);
            } else {
                return cmp;
            }
        }
    }); // 集合性
    private final HashMap<Integer, Integer> idToValue = new HashMap<>();
    private final HashMap<Integer, Tag> tags = new HashMap<>();
    private int money = 0;
    private int socialValue = 0;
    private final ArrayList<Message> messages = new ArrayList<>(); // 集合性

    public MyPerson(int id, String name, int age) {
        this.id = id;
        this.name = name;
        this.age = age;
    }

    @Override
    public int getId() {
        return id;
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public int getAge() {
        return age;
    }

    @Override
    public boolean containsTag(int id) {
        return tags.containsKey(id);
    }

    @Override
    public Tag getTag(int id) {
        if (containsTag(id)) {
            return tags.get(id);
        }
        return null;
    }

    @Override
    public void addTag(Tag tag) {
        tags.put(tag.getId(), tag);
    }

    @Override
    public void delTag(int id) {
        tags.remove(id);

    }

    public Set<Integer> getAcquaintance() {
        return idToValue.keySet();
    }

    public void link(Person person, int val) {
        idToValue.put(person.getId(), val);
        acquaintance.add(person);
    }

    public void unlink(Person person) {
        acquaintance.remove(person);
        idToValue.remove(person.getId());
    }

    public void updateValue(Person person, int newValue) {
        int id = person.getId();
        acquaintance.remove(person);
        idToValue.replace(id, newValue);
        acquaintance.add(person);
    }

    @Override
    public boolean isLinked(Person person) {
        return equals(person) || acquaintance.contains(person);
    }

    @Override
    public int queryValue(Person person) {
        if (!acquaintance.contains(person)) {
            return 0;
        } else {
            return idToValue.get(person.getId());
        }
    }

    @Override
    public void addSocialValue(int num) {
        socialValue += num;
    }

    @Override
    public int getSocialValue() {
        return socialValue;
    }

    public void addMessage(Message mes) {
        messages.add(0, mes);
    }

    @Override
    public List<Message> getMessages() {
        // TODO
        return new ArrayList<>(messages);
    }

    @Override
    public List<Message> getReceivedMessages() {
        // TODO performance?
        return messages.stream().limit(5).collect(Collectors.toList());
    }

    @Override
    public void addMoney(int num) {
        money += num;
    }

    @Override
    public int getMoney() {
        return money;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj instanceof Person) {
            return ((Person) obj).getId() == id;
        } else {
            return false;
        }
    }

    public boolean strictEquals(Person person) {
        return true;
    }

    public int getBest() {
        return acquaintance.first().getId();
    }

    @Override
    public String toString() {
        return "Person " + id;
    }

    public void clearNotices() {
        messages.removeIf(mes -> mes instanceof NoticeMessage);
    }
}
