import com.oocourse.library2.LibraryBookId;
import com.oocourse.library2.LibraryReqCmd;
import com.oocourse.library2.LibraryRequest;
import com.oocourse.library2.LibrarySystem;

import java.time.LocalDate;
import java.util.HashMap;
import java.util.Map;

public class Circulation {
    private final Facebook facebook = Facebook.INSTANCE;
    private final Bookstore bookstore = Controller.BOOKSHELF;
    private final Bookstore ccStore = Controller.CCSTORE;
    private final Bookstore circulationStore;
    private final HashMap<LibraryBookId, Integer> uoTimes = new HashMap<>();

    public Circulation(Bookstore circulationStore) {
        this.circulationStore = circulationStore;
    }

    public void handleBorrow(LibraryReqCmd reqCmd) {
        LibraryRequest req = reqCmd.getRequest();
        LibraryBookId bookId = req.getBookId();
        if (bookId.isTypeA() || bookId.isTypeAU()) {
            LibrarySystem.PRINTER.reject(reqCmd);
            return;
        }
        if (!bookstore.hasBook(bookId) && !ccStore.hasBook(bookId)) {
            LibrarySystem.PRINTER.reject(reqCmd);
            return;
        }
        if (bookId.isFormal()) {
            bookstore.take(bookId);
        } else {
            ccStore.take(bookId);
        }
        if (facebook.canBorrow(bookId, req.getStudentId())) {
            facebook.recordBorrow(reqCmd);
            LibrarySystem.PRINTER.accept(reqCmd);
        } else {
            circulationStore.put(bookId);
            LibrarySystem.PRINTER.reject(reqCmd);
        }
    }

    public void handleReturn(LibraryReqCmd reqCmd) {
        LibraryRequest req = reqCmd.getRequest();
        LocalDate today = reqCmd.getDate();
        LocalDate dueDate = facebook.getDueDay(req.getBookId(), req.getStudentId());
        facebook.recordReturn(req.getBookId(), req.getStudentId());
        circulationStore.put(req.getBookId());
        if (today.isAfter(dueDate)) {
            LibrarySystem.PRINTER.accept(reqCmd, "overdue");
        } else {
            LibrarySystem.PRINTER.accept(reqCmd, "not overdue");
        }
        if (!req.getBookId().isFormal()) {
            if (!uoTimes.containsKey(req.getBookId())) {
                uoTimes.put(req.getBookId(), 1);
            } else {
                uoTimes.replace(req.getBookId(), uoTimes.get(req.getBookId()) + 1);
            }
        }
    }

    public Map<LibraryBookId, Integer> getBooks() {
        return circulationStore.getBooks();
    }

    public boolean toUpgrade(LibraryBookId name) {
        if (name.isFormal()) {
            return false;
        }
        return uoTimes.getOrDefault(name, 0) >= 2;
    }
}
