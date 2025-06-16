package exception;

import com.oocourse.spec3.exceptions.RelationNotFoundException;

import java.util.HashMap;

public class MyRelationNotFoundException extends RelationNotFoundException {
    private static int total = 0;
    private static final HashMap<Integer, Integer> idToCnt = new HashMap<>();
    private static int currId1;
    private static int currId2;

    public MyRelationNotFoundException(int id1, int id2) {
        total++;
        addId(id1);
        addId(id2);
        if (id1 < id2) {
            currId1 = id1;
            currId2 = id2;
        } else {
            currId1 = id2;
            currId2 = id1;
        }
    }

    private void addId(int id) {
        if (idToCnt.containsKey(id)) {
            idToCnt.replace(id, idToCnt.get(id) + 1);
        } else {
            idToCnt.put(id, 1);
        }
    }

    @Override
    public void print() {
        System.out.printf("rnf-%d, %d-%d, %d-%d\n", total, currId1, idToCnt.get(currId1), currId2,
                idToCnt.get(currId2));
    }
}
