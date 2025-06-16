import com.oocourse.spec1.main.Person;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

public class MyPerson implements Person {
    private final int id;
    private final String name;
    private final int age;
    /*@ invariant acquaintance != null && value != null && acquaintance.length == value.length &&
      @  (\forall int i,j; 0 <= i && i < j && j < acquaintance.length;
      @   !acquaintance[i].equals(acquaintance[j]));*/
    private final HashSet<Person> acquaintance; // 集合性
    private final HashMap<Integer, Integer> idToValue;

    public MyPerson(int id, String name, int age) {
        this.id = id;
        this.name = name;
        this.age = age;
        this.acquaintance = new HashSet<>();
        this.idToValue = new HashMap<>();
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

    public Set<Integer> getAcquaintance() {
        return idToValue.keySet();
    }

    public void link(Person person, int val) {
        acquaintance.add(person);
        idToValue.put(person.getId(), val);
    }

    public void unlink(Person person) {
        acquaintance.remove(person);
        idToValue.remove(person.getId());
    }

    public void updateValue(int id, int newValue) {
        idToValue.replace(id, newValue);
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
}
