import com.oocourse.spec2.main.Person;
import com.oocourse.spec2.main.Tag;

import java.util.Comparator;
import java.util.HashMap;
import java.util.Set;
import java.util.TreeSet;

public class MyPerson implements Person {
    private final int id;
    private final String name;
    private final int age;
    /*@ invariant acquaintance != null && value != null && acquaintance.length == value.length &&
      @  (\forall int i,j; 0 <= i && i < j && j < acquaintance.length;
      @   !acquaintance[i].equals(acquaintance[j]));*/
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
}
