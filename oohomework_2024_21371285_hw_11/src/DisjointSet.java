import com.oocourse.spec3.main.Person;

import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.HashSet;

public class DisjointSet {
    // 并查集
    private final HashMap<Integer, Person> persons;
    private final HashMap<Integer, Integer> pa = new HashMap<>();

    DisjointSet(HashMap<Integer, Person> persons) {
        this.persons = persons;
    }

    public int find(int id) {
        if (pa.get(id) != id) {
            pa.replace(id, find(pa.get(id)));
        }
        return pa.get(id);
    }

    public void union(int x, int y) {
        int paX = find(x);
        int paY = find(y);
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

    public void unlink(int x, int y) {
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

    public void add(int id) {
        pa.put(id, id);
    }
}
