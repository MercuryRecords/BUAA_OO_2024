import com.oocourse.spec1.exceptions.EqualPersonIdException;
import com.oocourse.spec1.exceptions.PersonIdNotFoundException;
import com.oocourse.spec1.exceptions.RelationNotFoundException;
import com.oocourse.spec1.main.Person;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class MyTest {
    private MyNetwork network;
    private MyNetwork sdNetwork;
    @Before
    public void setUp() throws Exception {
        network = new MyNetwork();
        sdNetwork = new MyNetwork();
        for (int i = 0; i < 40; i++) {
            MyPerson person1 = new MyPerson(i, "", 18);
            MyPerson person2 = new MyPerson(i, "", 18);
            network.addPerson(person1);
            sdNetwork.addPerson(person2);
        }
        for (int i = 0; i < 40; i++) {
            for (int j = i + 1; j < 40; j++) {
                network.addRelation(i, j, 1);
                sdNetwork.addRelation(i, j, 1);
            }
        }
//        for (int i = 40; i < 80; i++) {
//            MyPerson person1 = new MyPerson(i, "", 18);
//            MyPerson person2 = new MyPerson(i, "", 18);
//            network.addPerson(person1);
//            sdNetwork.addPerson(person2);
//        }
    }

    @Test
    public void testQueryTripleSum(){
        for (int i = 0; i < 40; i += 2) {
            int id2 = i + 1;
            try {
                network.modifyRelation(i, id2, -2);
                sdNetwork.modifyRelation(i, id2, -2);
                int res = network.queryTripleSum();
                assertEquals(res, sdQueryTripleSum());
                if (sdNetwork.getPersons() != null && network.getPersons() != null) {
                    Person[] prs1 = sdNetwork.getPersons();
                    Person[] prs2 = network.getPersons();
                    assertEquals(prs1.length, prs2.length);
                    for (int j = 0; j < prs1.length; j++) {
                        assertTrue(((MyPerson) prs1[j]).strictEquals((MyPerson) prs2[j]));
                    }
                }
            } catch (RelationNotFoundException e) {
                e.print();
            } catch (PersonIdNotFoundException e) {
                e.print();
            } catch (EqualPersonIdException e) {
                e.print();
            }
        }
    }

    private int sdQueryTripleSum() {
        int ret = 0;
        if (sdNetwork.getPersons() != null) {
            int len = sdNetwork.getPersons().length;
            for (int i = 0; i < len; i++) {
                for (int j = i + 1; j < len; j++) {
                    for (int k = j + 1; k < len; k++) {
                        if (sdNetwork.getPerson(i).isLinked(sdNetwork.getPerson(j)) &&
                            sdNetwork.getPerson(j).isLinked(sdNetwork.getPerson(k)) &&
                            sdNetwork.getPerson(k).isLinked(sdNetwork.getPerson(i))) {
                            ret++;
                        }
                    }
                }
            }
        } else {
            return sdNetwork.queryTripleSum();
        }
        return ret;
    }
}
