import com.oocourse.spec2.main.Person;
import com.oocourse.spec2.main.Tag;

import java.util.HashMap;

public class MyTag implements Tag {
    private final int id;
    private int valueSum = 0;
    private int ageSum = 0;
    private int agePowSum = 0;
    private final HashMap<Integer, Person> persons;

    public MyTag(int id) {
        this.id = id;
        persons = new HashMap<>();
    }

    @Override
    public int getId() {
        return id;
    }

    @Override
    public boolean equals(Object object) {
        if (object instanceof Tag) {
            return ((Tag) object).getId() == id;
        }
        return false;
    }

    @Override
    public void addPerson(Person person) {
        for (Person pr : persons.values()) {
            if (person.isLinked(pr)) {
                valueSum += 2 * person.queryValue(pr);
            }
        }
        persons.put(person.getId(), person);
        int age = person.getAge();
        ageSum += age;
        agePowSum += age * age;
    }

    @Override
    public boolean hasPerson(Person person) {
        return persons.containsKey(person.getId());
    }

    @Override
    public int getValueSum() {
        return valueSum;
    }

    @Override
    public int getAgeMean() {
        if (!persons.isEmpty()) {
            return ageSum / persons.size();
        }
        return 0;
    }

    @Override
    public int getAgeVar() {
        if (!persons.isEmpty()) {
            int mean = ageSum / persons.size();
            return (agePowSum - 2 * mean * ageSum + mean * mean * persons.size()) / persons.size();
        }
        return 0;
    }

    @Override
    public void delPerson(Person person) {
        int age = person.getAge();
        ageSum -= age;
        agePowSum -= age * age;
        persons.remove(person.getId());
        for (Person pr : persons.values()) {
            if (person.isLinked(pr)) {
                valueSum -= 2 * person.queryValue(pr);
            }
        }
    }

    @Override
    public int getSize() {
        return persons.size();
    }

    public void updateValue(int oldValue, int newValue) {
        valueSum += newValue > 0 ? newValue - oldValue : -oldValue;
    }
}