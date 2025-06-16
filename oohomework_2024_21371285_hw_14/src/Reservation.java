import com.oocourse.library2.LibraryBookId;
import com.oocourse.library2.LibraryMoveInfo;
import com.oocourse.library2.LibraryReqCmd;
import com.oocourse.library2.LibraryRequest;
import com.oocourse.library2.LibrarySystem;
import javafx.util.Pair;

import java.time.LocalDate;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;

public class Reservation {
    private final Facebook facebook = Facebook.INSTANCE;
    private final Bookstore bookshelf = Controller.BOOKSHELF;
    private final Bookstore reservationStore;
    private final LinkedList<LibraryRequest> unhandledReqs = new LinkedList<>();
    private final HashMap<String, Bookstore> bookByUser = new HashMap<>(); // 已经到达的预留书籍
    private final LinkedList<Pair<LocalDate, LibraryRequest>> handledReqs = new LinkedList<>();

    public Reservation(Bookstore reservationStore) {
        this.reservationStore = reservationStore;
    }

    public void handleOrder(LibraryReqCmd reqCmd) {
        LibraryRequest req = reqCmd.getRequest();
        LibraryBookId bookId = req.getBookId();
        String studentId = req.getStudentId();
        if (bookId.isFormal() && facebook.canBorrow(bookId, studentId)) {
            facebook.recordOrder(bookId);
            unhandledReqs.add(req);
            LibrarySystem.PRINTER.accept(reqCmd);
        } else {
            LibrarySystem.PRINTER.reject(reqCmd);
        }
    }

    public void handlePick(LibraryReqCmd reqCmd) {
        LibraryRequest req = reqCmd.getRequest();
        if (!bookByUser.containsKey(req.getStudentId())) {
            LibrarySystem.PRINTER.reject(reqCmd);
        } else if (!bookByUser.get(req.getStudentId()).hasBook(req.getBookId())) {
            LibrarySystem.PRINTER.reject(reqCmd);
        } else if (!facebook.canBorrow(req.getBookId(), req.getStudentId())) {
            LibrarySystem.PRINTER.reject(reqCmd);
        } else {
            reservationStore.take(req.getBookId());
            bookByUser.get(req.getStudentId()).take(req.getBookId());
            facebook.recordBorrow(reqCmd);
            // 取书成功记录预约结束
            facebook.recordUnorder(req.getBookId());

            Iterator<Pair<LocalDate, LibraryRequest>> it = handledReqs.iterator();
            while (it.hasNext()) {
                LibraryRequest request = it.next().getValue();
                if (request.getStudentId().equals(req.getStudentId()) &&
                        request.getBookId().equals(req.getBookId())) {
                    it.remove();
                    break;
                }
            }
            LibrarySystem.PRINTER.accept(reqCmd);
        }
    }

    public LinkedList<LibraryMoveInfo> returnExpired(LocalDate cutDate) {
        LinkedList<LibraryMoveInfo> infos = new LinkedList<>();
        Iterator<Pair<LocalDate, LibraryRequest>> it = handledReqs.iterator();
        while (it.hasNext()) {
            Pair<LocalDate, LibraryRequest> pair = it.next();
            LocalDate date = pair.getKey();
            if (date.isBefore(cutDate)) {
                LibraryRequest req = pair.getValue();
                bookByUser.get(req.getStudentId()).take(req.getBookId());
                reservationStore.take(req.getBookId());
                bookshelf.put(req.getBookId());
                // 未取书预约失效
                facebook.recordUnorder(req.getBookId());
                infos.add(new LibraryMoveInfo(req.getBookId(), "ao", "bs"));
                it.remove();
            } else {
                break;
            }
        }
        return infos;
    }

    public LinkedList<LibraryMoveInfo> prepareOrdered(LocalDate date) {
        LinkedList<LibraryMoveInfo> infos = new LinkedList<>();
        Iterator<LibraryRequest> it = unhandledReqs.iterator();
        while (it.hasNext()) {
            LibraryRequest req = it.next();
            if (bookshelf.hasBook(req.getBookId())) {
                trySetBookStore(req.getStudentId());
                bookshelf.take(req.getBookId());
                reservationStore.put(req.getBookId());
                bookByUser.get(req.getStudentId()).put(req.getBookId());
                handledReqs.add(new Pair<>(date, req));
                it.remove();
                infos.add(new LibraryMoveInfo(req.getBookId(), "bs", "ao", req.getStudentId()));
            }
        }
        return infos;
    }

    private void trySetBookStore(String studentId) {
        if (!bookByUser.containsKey(studentId)) {
            bookByUser.put(studentId, new Bookstore());
        }
    }
}
