import com.oocourse.spec1.exceptions.EqualPersonIdException;
import com.oocourse.spec1.exceptions.EqualRelationException;
import com.oocourse.spec1.exceptions.PersonIdNotFoundException;
import com.oocourse.spec1.exceptions.RelationNotFoundException;
import com.oocourse.spec1.main.Network;
import com.oocourse.spec1.main.Person;
import exception.MyEqualPersonIdException;
import exception.MyEqualRelationException;
import exception.MyPersonIdNotFoundException;
import exception.MyRelationNotFoundException;

import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

public class MyNetwork implements Network {

    /*@ invariant persons != null && (\forall int i,j; 0 <= i && i < j && j < persons.length;
                                      !persons[i].equals(persons[j]));*/
    private final HashMap<Integer, Person> persons;
    // 并查集
    private final HashMap<Integer, Integer> pa;
    private final HashMap<Integer, Integer> size;
    private int tripleSum = 0;
    private int blockSum = 0;

    public MyNetwork() {
        persons = new HashMap<>();
        pa = new HashMap<>();
        size = new HashMap<>();
    }

    private int paFind(int id) {
        if (pa.get(id) != id) {
            pa.replace(id, paFind(pa.get(id)));
        }
        return pa.get(id);
    }

    private void paUnion(int x, int y) {
        int paX = paFind(x);
        int paY = paFind(y);
        if (paX == paY) {
            return;
        }
        if (size.get(x) < size.get(y)) {
            //noinspection SuspiciousNameCombination
            paX ^= paY;
            //noinspection SuspiciousNameCombination
            paY ^= paX;
            //noinspection SuspiciousNameCombination
            paX ^= paY;
        }
        pa.replace(paY, paX); // 合并
        size.replace(paX, size.get(paY) + size.get(paX));
    }

    private void paUnlink(int x, int y) {
        pa.replace(x, null);
        // BFS
        paMark(y);
        if (pa.get(x) != null && pa.get(x) == y) {
            return;
        } else {
            pa.replace(x, x);
            paMark(x);
        }
    }

    private void paMark(int id) {
        ArrayDeque<Integer> queue = new ArrayDeque<>();
        HashSet<Integer> marked = new HashSet<>();
        queue.add(id);
        int deltaSize = 0;
        while (!queue.isEmpty()) {
            int currId = queue.remove();
            if (!marked.contains(currId)) {
                marked.add(currId);
                if (pa.get(currId) != null) {
                    int oldPa = pa.get(currId);
                    size.replace(oldPa, size.get(oldPa) - 1);
                }
                deltaSize++;
                // size.replace(id, size.get(id) + 1);
                pa.replace(currId, id);
                queue.addAll(((MyPerson) persons.get(currId)).getAcquaintance());
            }
        }
        size.replace(id, size.get(id) + deltaSize);
    }

    private void paRebuild() {
        for (Integer id: persons.keySet()) {
            pa.replace(id, id);
        }
        for (Person person: persons.values()) {
            int id = person.getId();
            for (Integer acId: ((MyPerson) person).getAcquaintance()) {
                paUnion(id, acId);
            }
        }
    }

    @Override
    public boolean containsPerson(int id) {
        return persons.containsKey(id);
    }

    @Override
    public Person getPerson(int id) {
        if (!containsPerson(id)) {
            return null;
        } else {
            return persons.get(id);
        }
    }

    @Override
    public void addPerson(Person person) throws EqualPersonIdException {
        int id = person.getId();
        if (containsPerson(id)) {
            throw new MyEqualPersonIdException(id);
        } else {
            persons.put(id, person);
            pa.put(id, id);
            size.put(id, 1);
            blockSum++;
        }
    }

    @Override
    public void addRelation(int id1, int id2, int value) throws
            PersonIdNotFoundException, EqualRelationException {
        if (!containsPerson(id1)) {
            throw new MyPersonIdNotFoundException(id1);
        }
        if (!containsPerson(id2)) {
            throw new MyPersonIdNotFoundException(id2);
        }
        if (getPerson(id1).isLinked(getPerson(id2))) {
            throw new MyEqualRelationException(id1, id2); // id1 == id2 会抛出这个异常
        }
        if (getPerson(id1) instanceof MyPerson && getPerson(id2) instanceof MyPerson) {
            MyPerson p1 = (MyPerson) getPerson(id1);
            MyPerson p2 = (MyPerson) getPerson(id2);
            if (paFind(id1) != paFind(id2)) {
                blockSum--;
            }
            p1.link(p2, value);
            p2.link(p1, value);
            Set<Integer> interSet = new HashSet<>(p1.getAcquaintance());
            interSet.retainAll(p2.getAcquaintance());
            tripleSum += interSet.size();
            paUnion(id1, id2);
        }
    }

    @Override
    public void modifyRelation(int id1, int id2, int value) throws
            PersonIdNotFoundException, EqualPersonIdException, RelationNotFoundException {
        if (!containsPerson(id1)) {
            throw new MyPersonIdNotFoundException(id1);
        }
        if (!containsPerson(id2)) {
            throw new MyPersonIdNotFoundException(id2);
        }
        if (id1 == id2) {
            throw new MyEqualPersonIdException(id1);
        }
        if (!getPerson(id1).isLinked(getPerson(id2))) {
            throw new MyRelationNotFoundException(id1, id2);
        }
        if (getPerson(id1) instanceof MyPerson && getPerson(id2) instanceof MyPerson) {
            MyPerson p1 = (MyPerson) getPerson(id1);
            MyPerson p2 = (MyPerson) getPerson(id2);
            int newValue = p1.queryValue(p2) + value;
            if (newValue <= 0) {
                p1.unlink(p2);
                p2.unlink(p1);
                Set<Integer> interSet = new HashSet<>(p1.getAcquaintance());
                interSet.retainAll(p2.getAcquaintance());
                tripleSum -= interSet.size();
                paUnlink(id1, id2);
                if (paFind(id1) != paFind(id2)) {
                    blockSum++;
                }
                // paRebuild();
            } else {
                p1.updateValue(id2, newValue);
                p2.updateValue(id1, newValue);
            }
        }
    }

    @Override
    public int queryValue(int id1, int id2) throws
            PersonIdNotFoundException, RelationNotFoundException {
        if (!containsPerson(id1)) {
            throw new MyPersonIdNotFoundException(id1);
        }
        if (!containsPerson(id2)) {
            throw new MyPersonIdNotFoundException(id2);
        }
        if (!getPerson(id1).isLinked(getPerson(id2))) {
            throw new MyRelationNotFoundException(id1, id2);
        }
        return getPerson(id1).queryValue(getPerson(id2));
    }

    @Override
    public boolean isCircle(int id1, int id2) throws PersonIdNotFoundException {
        if (!containsPerson(id1)) {
            throw new MyPersonIdNotFoundException(id1);
        }
        if (!containsPerson(id2)) {
            throw new MyPersonIdNotFoundException(id2);
        }
        return paFind(id1) == paFind(id2);
    }

    @Override
    public int queryBlockSum() {
        // i 严格大于 j -> 朴素而言，每两人只被查询一次
        // HashSet<Integer> branches = new HashSet<>();
        // for (Integer id: pa.keySet()) {
        //     branches.add(paFind(id));
        // }
        // return branches.size();
        return blockSum;
    }

    @Override
    public int queryTripleSum() {
        // i j k 严格递增 -> 每三个人只被查询一次
        return tripleSum;
    }

    public Person[] getPersons() {
        return null;
    }
}
