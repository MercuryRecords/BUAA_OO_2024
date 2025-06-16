import com.oocourse.spec2.exceptions.*;
import com.oocourse.spec2.main.Person;
import org.junit.Test;

import java.util.Random;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class MyTest {
    @Test
    public void testCoupleSum() {
        MyNetwork network = new MyNetwork();
        MyNetwork copy = new MyNetwork();
        Random random = new Random(20240505L);

        for (int times = 0; times < 10; times++) {
            for (int i = 0; i < 40; i++) {
                MyPerson pr1 = new MyPerson(i, String.valueOf(i), 18);
                MyPerson pr2 = new MyPerson(i, String.valueOf(i), 18);
                try {
                    network.addPerson(pr1);
                    copy.addPerson(pr2);
                } catch (EqualPersonIdException e) {
                    e.print();
                }
            }

            for (int i = 0; i < 500; i++) {
                int x = random.nextInt(100);
                int y = random.nextInt(100);
                int val = random.nextInt(200);

                try {
                    network.addRelation(x, y, val);
                    copy.addRelation(x, y, val);
                } catch (PersonIdNotFoundException e) {
                    e.print();
                } catch (EqualRelationException e) {
                    e.print();
                }
            }

            for (int i = 0; i < 200; i++) {
                int x = random.nextInt(100);
                int y = random.nextInt(100);
                int val = random.nextInt(200) - 200;

                try {
                    network.modifyRelation(x, y, val);
                    copy.modifyRelation(x, y, val);
                } catch (PersonIdNotFoundException e) {
                    e.print();
                } catch (EqualPersonIdException e) {
                    e.print();
                } catch (RelationNotFoundException e) {
                    e.print();
                }

                Person[] persons = copy.getPersons();
                int res = 0;
                for (Person person: persons) {
                    try {
                        int bestie = copy.queryBestAcquaintance(person.getId());
                        if (copy.queryBestAcquaintance(bestie) == person.getId()) {
                            res++;
                        }
                    } catch (PersonIdNotFoundException e) {
                        e.print();
                    } catch (AcquaintanceNotFoundException e) {
                        e.print();
                    }
                }
                assertEquals(res / 2, network.queryCoupleSum());
                Person[] people = network.getPersons();
                assertEquals(persons.length, people.length);
                for (int j = 0; j < people.length; j++) {
                    assertTrue(((MyPerson) people[j]).strictEquals(persons[j]));
                }
            }
        }

    }
}
