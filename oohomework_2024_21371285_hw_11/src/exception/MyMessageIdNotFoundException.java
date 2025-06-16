package exception;

import com.oocourse.spec3.exceptions.MessageIdNotFoundException;

import java.util.HashMap;

public class MyMessageIdNotFoundException extends MessageIdNotFoundException {
    private static int total = 0;
    private static final HashMap<Integer, Integer> idToCnt = new HashMap<>();
    private static int currId;

    public MyMessageIdNotFoundException(int id) {
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
        System.out.printf("minf-%d, %d-%d\n", total, currId, idToCnt.get(currId));
    }
}