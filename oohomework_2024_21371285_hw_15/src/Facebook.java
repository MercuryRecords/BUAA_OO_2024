import com.oocourse.library3.LibraryBookId;
import com.oocourse.library3.LibraryQcsCmd;
import com.oocourse.library3.LibraryReqCmd;
import com.oocourse.library3.LibrarySystem;
import com.oocourse.library3.annotation.SendMessage;

import java.time.LocalDate;
import java.util.HashMap;
import java.util.HashSet;

import static java.lang.Integer.min;

public class Facebook {
    public static final Facebook INSTANCE = new Facebook();
    private final Bookstore bookshelf = Controller.BOOKSHELF;
    /* 只记录持有的书和最后有效时间 */
    private final HashMap<String, HashMap<LibraryBookId, LocalDate>> user2book = new HashMap<>();
    private final HashMap<LibraryBookId, Integer> book2Orderednum = new HashMap<>();
    private final HashMap<String, Boolean> user2Btype = new HashMap<>();
    private final HashMap<String, Boolean> user2BUtype = new HashMap<>();
    private final HashMap<String, HashSet<LibraryBookId>> user2OrderedBook = new HashMap<>();
    private final HashMap<String, Boolean> user2OrderedBtypeBook = new HashMap<>();
    private final HashMap<String, Integer> user2CreditScore = new HashMap<>();
    private final HashMap<LibraryBookId, String> donatedBooks2User = new HashMap<>();
    private final HashMap<String, HashMap<LibraryBookId, Boolean>> bookRecorded = new HashMap<>();

    private Facebook() {
    }

    public boolean canBorrow(LibraryBookId bookId, String studentId) {
        if (!user2book.containsKey(studentId)) {
            register(studentId);
        }
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

    public boolean canOrder(LibraryBookId bookId, String studentId) {
        if (!canBorrow(bookId, studentId)) {
            return false;
        }
        if (user2CreditScore.get(studentId) < 0) {
            return false;
        }
        if (bookId.isTypeB() && user2OrderedBtypeBook.get(studentId)) {
            return false;
        }

        return !user2OrderedBook.get(studentId).contains(bookId);
    }

    public void recordBorrow(LibraryReqCmd reqCmd) {
        LibraryBookId bookId = reqCmd.getBookId();
        String studentId = reqCmd.getStudentId();
        LocalDate date = reqCmd.getDate();
        if (!user2book.containsKey(studentId)) {
            register(studentId);
        }
        user2book.get(studentId).put(bookId, calDueDay(bookId, date));
        bookRecorded.get(studentId).put(bookId, false);
        if (bookId.isTypeB()) {
            user2Btype.replace(studentId, true);
        }
        if (bookId.isTypeBU()) {
            user2BUtype.replace(studentId, true);
        }
    }

    public void recordReturn(LibraryBookId bookId, String studentId) {
        user2book.get(studentId).remove(bookId);
        bookRecorded.get(studentId).remove(bookId);
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
        user2OrderedBook.put(studentId, new HashSet<>());
        user2OrderedBtypeBook.put(studentId, false);
        user2Btype.put(studentId, false);
        user2BUtype.put(studentId, false);
        user2CreditScore.put(studentId, 10);
        bookRecorded.put(studentId, new HashMap<>());
    }

    public LocalDate getDueDay(LibraryBookId bookId, String studentId) {
        return user2book.get(studentId).get(bookId);
    }

    public void handleRenew(LibraryReqCmd reqCmd) {
        if (user2CreditScore.get(reqCmd.getStudentId()) < 0) {
            LibrarySystem.PRINTER.reject(reqCmd);
            return;
        }
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
        } else if (user2CreditScore.get(reqCmd.getStudentId()) < 0) {
            LibrarySystem.PRINTER.reject(reqCmd);
        } else {
            LibrarySystem.PRINTER.accept(reqCmd);
            user2book.get(reqCmd.getStudentId()).replace(reqCmd.getBookId(), dueDate.plusDays(30));
        }
    }

    @SendMessage(from = "Reservation", to = "Facebook")
    public void orderNewBook(String studentId, LibraryBookId bookId) {
        if (!book2Orderednum.containsKey(bookId)) {
            book2Orderednum.put(bookId, 1);
        } else {
            book2Orderednum.replace(bookId, book2Orderednum.get(bookId) + 1);
        }
        user2OrderedBook.get(studentId).add(bookId);
        if (bookId.isTypeB()) {
            user2OrderedBtypeBook.replace(studentId, true);
        }
    }

    @SendMessage(from = "Facebook", to = "Reservation")
    public void getOrderedBook(String studentId, LibraryBookId bookId) {
        book2Orderednum.replace(bookId, book2Orderednum.get(bookId) - 1);
        user2OrderedBook.get(studentId).remove(bookId);
        if (bookId.isTypeB()) {
            user2OrderedBtypeBook.replace(studentId, false);
        }
    }

    public void qcs(LibraryQcsCmd cmd) {
        LibrarySystem.PRINTER.info(cmd, user2CreditScore.getOrDefault(cmd.getStudentId(), 10));
    }

    public void addCreditScore(LibraryBookId name) {
        String id = donatedBooks2User.get(name);
        addCreditScore(id, 2);
    }

    public void addCreditScore(String studentId, int delta) {
        int newVal = min(user2CreditScore.get(studentId) + delta, 20);
        user2CreditScore.replace(studentId, newVal);
    }

    public void minusCreditScore(String studentId, int delta) {
        user2CreditScore.replace(studentId, user2CreditScore.get(studentId) - delta);
    }

    public void handleDonate(LibraryReqCmd reqCmd) {
        Controller.CCSTORE.put(reqCmd.getBookId());
        if (!user2book.containsKey(reqCmd.getStudentId())) {
            register(reqCmd.getStudentId());
        }
        donatedBooks2User.put(reqCmd.getBookId(), reqCmd.getStudentId());
        addCreditScore(reqCmd.getStudentId(), 2);
        LibrarySystem.PRINTER.accept(reqCmd);
    }

    public void recordOverdue(LocalDate date) {
        for (String name: user2book.keySet()) {
            HashMap<LibraryBookId, LocalDate> map = user2book.get(name);
            for (LibraryBookId bookId: map.keySet()) {
                if (!bookRecorded.get(name).get(bookId) && date.isAfter(map.get(bookId))) {
                    minusCreditScore(name, 2);
                    bookRecorded.get(name).replace(bookId, true);
                }
            }
        }
    }

    public int getCreditScore(String studentId) {
        return user2CreditScore.getOrDefault(studentId, 10);
    }
}
