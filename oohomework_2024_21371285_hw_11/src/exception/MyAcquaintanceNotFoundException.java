package exception;

import com.oocourse.spec3.exceptions.AcquaintanceNotFoundException;

import java.util.HashMap;

public class MyAcquaintanceNotFoundException extends AcquaintanceNotFoundException {
    private static int total = 0;
    private static final HashMap<Integer, Integer> idToCnt = new HashMap<>();
    private static int currId;

    public MyAcquaintanceNotFoundException(int id) {
        total++;
        if (idToCnt.containsKey(id)) {
            idToCnt.replace(id, idToCnt.get(id) + 1);
        } else {
            idToCnt.put(id, 1);
        }
        currId = id;
    }

    @Override
    public void print() {
        System.out.printf("anf-%d, %d-%d\n", total, currId, idToCnt.get(currId));
    }
}
