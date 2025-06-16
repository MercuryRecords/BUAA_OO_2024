import com.oocourse.library2.LibraryBookId;
import com.oocourse.library2.LibraryReqCmd;
import com.oocourse.library2.LibrarySystem;

import java.time.LocalDate;
import java.util.HashMap;

public class Facebook {
    public static final Facebook INSTANCE = new Facebook();
    private final Bookstore bookshelf = Controller.BOOKSHELF;
    /* 只记录持有的书和最后有效时间 */
    private final HashMap<String, HashMap<LibraryBookId, LocalDate>> user2book = new HashMap<>();
    private final HashMap<LibraryBookId, Integer> book2Orderednum = new HashMap<>();
    private final HashMap<String, Boolean> user2Btype = new HashMap<>();
    private final HashMap<String, Boolean> user2BUtype = new HashMap<>();

    private Facebook() {
    }

    public boolean canBorrow(LibraryBookId bookId, String studentId) {
        if (bookId.isTypeA() || bookId.isTypeAU()) {
            return false;
        } else if (bookId.isTypeB()) {
            if (!user2Btype.containsKey(studentId)) {
                return true;
            }
            return !user2Btype.get(studentId);
        } else if (bookId.isTypeBU()) {
            if (!user2BUtype.containsKey(studentId)) {
                return true;
            }
            return !user2BUtype.get(studentId);

        } else {
            if (!user2book.containsKey(studentId)) {
                return true;
            }
            return !user2book.get(studentId).containsKey(bookId);
        }
    }

    public void recordBorrow(LibraryReqCmd reqCmd) {
        LibraryBookId bookId = reqCmd.getBookId();
        String studentId = reqCmd.getStudentId();
        LocalDate date = reqCmd.getDate();
        if (!user2book.containsKey(studentId)) {
            register(studentId);
        }
        user2book.get(studentId).put(bookId, calDueDay(bookId, date));
        if (bookId.isTypeB()) {
            user2Btype.replace(studentId, true);
        }
        if (bookId.isTypeBU()) {
            user2BUtype.replace(studentId, true);
        }
    }

    public void recordReturn(LibraryBookId bookId, String studentId) {
        user2book.get(studentId).remove(bookId);
        if (bookId.isTypeB()) {
            user2Btype.replace(studentId, false);
        }
        if (bookId.isTypeBU()) {
            user2BUtype.replace(studentId, false);
        }
    }

    private LocalDate calDueDay(LibraryBookId bookId, LocalDate date) {
        if (bookId.isTypeB()) {
            return date.plusDays(30);
        } else if (bookId.isTypeC()) {
            return date.plusDays(60);
        } else if (bookId.isTypeBU()) {
            return date.plusDays(7);
        } else {
            return date.plusDays(14);
        }
    }

    private void register(String studentId) {
        user2book.put(studentId, new HashMap<>());
        user2Btype.put(studentId, false);
        user2BUtype.put(studentId, false);
    }

    public LocalDate getDueDay(LibraryBookId bookId, String studentId) {
        return user2book.get(studentId).get(bookId);
    }

    public void handleRenew(LibraryReqCmd reqCmd) {
        if (!reqCmd.getBookId().isFormal()) {
            LibrarySystem.PRINTER.reject(reqCmd);
            return;
        }
        if (!user2book.get(reqCmd.getStudentId()).containsKey(reqCmd.getBookId())) {
            LibrarySystem.PRINTER.reject(reqCmd);
            return;
        }
        LocalDate dueDate = user2book.get(reqCmd.getStudentId()).get(reqCmd.getBookId());
        LocalDate today = reqCmd.getDate();
        if (!(today.isAfter(dueDate.minusDays(5)) && today.isBefore(dueDate.plusDays(1)))) {
            LibrarySystem.PRINTER.reject(reqCmd);
        }
        else if (book2Orderednum.getOrDefault(reqCmd.getBookId(), 0) > 0 &&
                !bookshelf.hasBook(reqCmd.getBookId())) {
            LibrarySystem.PRINTER.reject(reqCmd);
        } else {
            LibrarySystem.PRINTER.accept(reqCmd);
            user2book.get(reqCmd.getStudentId()).replace(reqCmd.getBookId(), dueDate.plusDays(30));
        }
    }

    public void recordOrder(LibraryBookId bookId) {
        if (!book2Orderednum.containsKey(bookId)) {
            book2Orderednum.put(bookId, 1);
        } else {
            book2Orderednum.replace(bookId, book2Orderednum.get(bookId) + 1);
        }
    }

    public void recordUnorder(LibraryBookId bookId) {
        book2Orderednum.replace(bookId, book2Orderednum.get(bookId) - 1);
    }
}
