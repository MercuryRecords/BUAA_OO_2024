import com.oocourse.spec2.exceptions.AcquaintanceNotFoundException;
import com.oocourse.spec2.exceptions.EqualPersonIdException;
import com.oocourse.spec2.exceptions.EqualRelationException;
import com.oocourse.spec2.exceptions.EqualTagIdException;
import com.oocourse.spec2.exceptions.PathNotFoundException;
import com.oocourse.spec2.exceptions.PersonIdNotFoundException;
import com.oocourse.spec2.exceptions.RelationNotFoundException;
import com.oocourse.spec2.exceptions.TagIdNotFoundException;
import com.oocourse.spec2.main.Network;
import com.oocourse.spec2.main.Person;
import com.oocourse.spec2.main.Tag;
import exception.MyAcquaintanceNotFoundException;
import exception.MyEqualPersonIdException;
import exception.MyEqualRelationException;
import exception.MyEqualTagIdException;
import exception.MyPathNotFoundException;
import exception.MyPersonIdNotFoundException;
import exception.MyRelationNotFoundException;
import exception.MyTagIdNotFoundException;

import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class MyNetwork implements Network {

    /*@ invariant persons != null && (\forall int i,j; 0 <= i && i < j && j < persons.length;
                                      !persons[i].equals(persons[j]));*/
    private final HashMap<Integer, Person> persons = new HashMap<>();
    // 并查集
    private final HashMap<Integer, Integer> pa = new HashMap<>();
    private final HashMap<Integer, HashMap<Integer, HashSet<Tag>>> followerToTags = new HashMap<>();
    private int tripleSum = 0;
    private int blockSum = 0;
    private int coupleSum = 0;
    private boolean coupleCached = false;

    public MyNetwork() {
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
        //if (size.get(x) < size.get(y)) {
        //    //noinspection SuspiciousNameCombination
        //    paX ^= paY;
        //    //noinspection SuspiciousNameCombination
        //    paY ^= paX;
        //    //noinspection SuspiciousNameCombination
        //    paX ^= paY;
        //}
        pa.replace(paY, paX); // 合并
        //size.replace(paX, size.get(paY) + size.get(paX));
    }

    private void paUnlink(int x, int y) {
        pa.replace(x, x);
        // BFS
        paMark(y);
        if (pa.get(x) != y) {
            paMark(x);
        }
    }

    private void paMark(int id) {
        ArrayDeque<Integer> queue = new ArrayDeque<>();
        HashSet<Integer> marked = new HashSet<>();
        queue.add(id);
        //int deltaSize = 0;
        while (!queue.isEmpty()) {
            int currId = queue.remove();
            if (!marked.contains(currId)) {
                marked.add(currId);
                //int oldPa = pa.get(currId);
                //size.replace(oldPa, size.get(oldPa) - 1);
                //deltaSize++;
                // size.replace(id, size.get(id) + 1);
                pa.replace(currId, id);
                queue.addAll(((MyPerson) persons.get(currId)).getAcquaintance());
            }
        }
        //size.replace(id, size.get(id) + deltaSize);
    }

    @Override
    public boolean containsPerson(int id) {
        return persons.containsKey(id);
    }

    private void findPersonId(int id1, int id2) throws MyPersonIdNotFoundException {
        if (!persons.containsKey(id1)) {
            throw new MyPersonIdNotFoundException(id1);
        }
        if (!persons.containsKey(id2)) {
            throw new MyPersonIdNotFoundException(id2);
        }
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
    public Person getPerson(int id) {
        return persons.getOrDefault(id, null);
    }

    @Override
    public void addPerson(Person person) throws EqualPersonIdException {
        int id = person.getId();
        if (persons.containsKey(id)) {
            throw new MyEqualPersonIdException(id);
        } else {
            persons.put(id, person);
            pa.put(id, id);
            followerToTags.put(id, new HashMap<>());
            //size.put(id, 1);
            blockSum++;
        }
    }

    @Override
    public void addRelation(int id1, int id2, int value) throws
            PersonIdNotFoundException, EqualRelationException {
        findPersonId(id1, id2);
        if (getPerson(id1).isLinked(getPerson(id2))) {
            throw new MyEqualRelationException(id1, id2); // id1 == id2 会抛出这个异常
        }
        MyPerson p1 = (MyPerson) getPerson(id1);
        MyPerson p2 = (MyPerson) getPerson(id2);
        if (p1.getAcquaintance().isEmpty() || p2.getAcquaintance().isEmpty()) {
            coupleCached = false;
        } else if ((value >= p1.queryValue(persons.get(p1.getBest()))) ||
                   (value >= p2.queryValue(persons.get(p2.getBest())))) {
            coupleCached = false;
        }

        if (paFind(id1) != paFind(id2)) {
            blockSum--;
        }
        p1.link(p2, value);
        p2.link(p1, value);
        Set<Integer> interSet = new HashSet<>(p1.getAcquaintance());
        interSet.retainAll(p2.getAcquaintance());
        tripleSum += interSet.size();
        paUnion(id1, id2);

        updateRelationValueToTag(id1, id2, 0, 2 * value);

    }

    @Override
    public void modifyRelation(int id1, int id2, int value) throws
            PersonIdNotFoundException, EqualPersonIdException, RelationNotFoundException {
        findPersonId(id1, id2);
        if (id1 == id2) {
            throw new MyEqualPersonIdException(id1);
        }
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
            paUnlink(id1, id2);
            if (paFind(id1) != paFind(id2)) {
                blockSum++;
            }
            cleanTags(id1, id2);
            cleanTags(id2, id1);
            // paRebuild();
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
                if (tag.hasPerson(persons.get(id2))) {
                    ((MyTag) tag).updateValue(oldVal, newVal);
                }
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
        return paFind(id1) == paFind(id2);
    }

    @Override
    public int queryBlockSum() {
        // i 严格大于 j -> 朴素而言，每两人只被查询一次
        return blockSum;
    }

    @Override
    public int queryTripleSum() {
        // i j k 严格递增 -> 每三个人只被查询一次
        return tripleSum;
    }

    @Override
    public void addTag(int personId, Tag tag) throws
            PersonIdNotFoundException, EqualTagIdException {
        if (!persons.containsKey(personId)) {
            throw new MyPersonIdNotFoundException(personId);
        }
        Person person = persons.get(personId);
        int tagId = tag.getId();
        if (person.containsTag(tagId)) {
            throw new MyEqualTagIdException(tagId);
        }
        person.addTag(tag);
    }

    @Override
    public void addPersonToTag(int personId1, int personId2, int tagId) throws
            PersonIdNotFoundException, RelationNotFoundException, TagIdNotFoundException,
            EqualPersonIdException {
        findPersonId(personId1, personId2);
        if (personId1 == personId2) {
            throw new MyEqualPersonIdException(personId1);
        }
        findRelation(personId2, personId1);
        findTagId(personId2, tagId);
        Tag tag = persons.get(personId2).getTag(tagId);
        if (tag.hasPerson(persons.get(personId1))) {
            throw new MyEqualPersonIdException(personId1);
        }
        if (tag.getSize() <= 1111) {
            tag.addPerson(persons.get(personId1));
            HashMap<Integer, HashSet<Tag>> map = followerToTags.get(personId1);
            if (map.containsKey(personId2)) {
                map.get(personId2).add(tag);
            } else {
                HashSet<Tag> tags = new HashSet<>();
                tags.add(tag);
                map.put(personId2, tags);
            }
        }
    }

    @Override
    public int queryTagValueSum(int personId, int tagId) throws
            PersonIdNotFoundException, TagIdNotFoundException {
        if (!persons.containsKey(personId)) {
            throw new MyPersonIdNotFoundException(personId);
        }
        findTagId(personId, tagId);
        return persons.get(personId).getTag(tagId).getValueSum();
    }

    @Override
    public int queryTagAgeVar(int personId, int tagId) throws
            PersonIdNotFoundException, TagIdNotFoundException {
        if (!persons.containsKey(personId)) {
            throw new MyPersonIdNotFoundException(personId);
        }
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
        if (!tag.hasPerson(person1)) {
            throw new MyPersonIdNotFoundException(personId1);
        }
        tag.delPerson(person1);
        HashMap<Integer, HashSet<Tag>> map = followerToTags.get(personId1);
        HashSet<Tag> tags = map.get(personId2);
        tags.remove(tag);
        if (tags.isEmpty()) {
            map.remove(personId2);
        }
    }

    @Override
    public void delTag(int personId, int tagId) throws
            PersonIdNotFoundException, TagIdNotFoundException {
        if (!persons.containsKey(personId)) {
            throw new MyPersonIdNotFoundException(personId);
        }
        findTagId(personId, tagId);
        persons.get(personId).delTag(tagId);
    }

    @Override
    public int queryBestAcquaintance(int id) throws
            PersonIdNotFoundException, AcquaintanceNotFoundException {
        if (!persons.containsKey(id)) {
            throw new MyPersonIdNotFoundException(id);
        }
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
        if (paFind(id1) != paFind(id2)) {
            throw new MyPathNotFoundException(id1, id2);
        }

        if (id1 == id2) {
            return 0;
        }
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
                if (updateBiBfs(queue1, visited1, visited2)) {
                    break;
                }
            } else {
                if (updateBiBfs(queue2, visited2, visited1)) {
                    break;
                }
            }
        }

        return dis;
    }

    private boolean updateBiBfs(ArrayDeque<Integer> q, Set<Integer> visited, Set<Integer> other) {
        ArrayDeque<Integer> thisFloor = new ArrayDeque<>(q);
        while (!thisFloor.isEmpty()) {
            Integer curr = q.pollFirst();
            thisFloor.removeFirst();
            for (int ac : ((MyPerson) persons.get(curr)).getAcquaintance()) {
                if (visited.contains(ac)) {
                    continue;
                }
                if (other.contains(ac)) {
                    return true;
                }
                visited.add(ac);
                q.add(ac);
            }
        }
        return false;
    }

    public Person[] getPersons() {
        Person[] ret = new Person[persons.size()];
        int i = 0;
        for (Person person: persons.values()) {
            ret[i] = person;
            i++;
        }
        return ret;
    }
}
