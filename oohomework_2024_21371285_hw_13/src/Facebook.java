import com.oocourse.library1.LibraryBookId;

import java.util.HashMap;
import java.util.HashSet;

public class Facebook {
    public static final Facebook INSTANCE = new Facebook();
    private final HashMap<String, HashSet<LibraryBookId>> user2book = new HashMap<>();  // 只记录持有的书
    private final HashMap<String, Boolean> user2Btype = new HashMap<>();

    private Facebook() {
    }

    public boolean canBorrow(LibraryBookId bookId, String studentId) {
        if (bookId.isTypeA()) {
            return false;
        } else if (bookId.isTypeB()) {
            if (!user2Btype.containsKey(studentId)) {
                return true;
            }
            return !user2Btype.get(studentId);
        } else {
            if (!user2book.containsKey(studentId)) {
                return true;
            }
            return !user2book.get(studentId).contains(bookId);
        }
    }

    public void recordBorrow(LibraryBookId bookId, String studentId) {
        if (!user2book.containsKey(studentId)) {
            register(studentId);
        }
        user2book.get(studentId).add(bookId);
        if (bookId.isTypeB()) {
            user2Btype.replace(studentId, true);
        }
    }

    private void register(String studentId) {
        user2book.put(studentId, new HashSet<>());
        user2Btype.put(studentId, false);
    }

    public void recordReturn(LibraryBookId bookId, String studentId) {
        user2book.get(studentId).remove(bookId);
        if (bookId.isTypeB()) {
            user2Btype.replace(studentId, false);
        }
    }
}
