import com.oocourse.library1.LibraryBookId;
import com.oocourse.library1.LibraryRequest;
import com.oocourse.library1.LibrarySystem;

import java.time.LocalDate;

public class Circulation {
    private final Facebook facebook = Facebook.INSTANCE;
    private final Bookstore bookstore;
    private final Bookstore circulationStore;

    public Circulation(Bookstore bookstore, Bookstore circulationStore) {
        this.bookstore = bookstore;
        this.circulationStore = circulationStore;
    }

    public void handleBorrow(LocalDate date, LibraryRequest req) {
        LibraryBookId bookId = req.getBookId();
        if (!bookstore.hasBook(bookId) || bookId.isTypeA()) {
            LibrarySystem.PRINTER.reject(date, req);
            return;
        }
        bookstore.take(bookId);
        if (facebook.canBorrow(bookId, req.getStudentId())) {
            facebook.recordBorrow(bookId, req.getStudentId());
            LibrarySystem.PRINTER.accept(date, req);
        } else {
            circulationStore.put(bookId);
            LibrarySystem.PRINTER.reject(date, req);
        }
    }

    public void handleReturn(LocalDate date, LibraryRequest req) {
        facebook.recordReturn(req.getBookId(), req.getStudentId());
        circulationStore.put(req.getBookId());
        LibrarySystem.PRINTER.accept(date, req);
    }
}
