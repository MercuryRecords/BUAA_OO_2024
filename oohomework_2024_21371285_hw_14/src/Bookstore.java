import com.oocourse.library2.LibraryBookId;
import com.oocourse.library2.LibraryReqCmd;
import com.oocourse.library2.LibrarySystem;

import java.time.LocalDate;
import java.util.HashMap;
import java.util.Map;

public class Bookstore {
    private final Map<LibraryBookId, Integer> books;

    public Bookstore() {
        this.books = new HashMap<>();
    }

    public Bookstore(Map<LibraryBookId, Integer> books) {
        this.books = books;
    }

    public void query(LibraryReqCmd reqCmd) {
        LocalDate date = reqCmd.getDate();
        LibraryBookId bookId = reqCmd.getBookId();
        LibrarySystem.PRINTER.info(date, bookId, books.getOrDefault(bookId, 0));
    }

    public boolean hasBook(LibraryBookId bookId) {
        if (!books.containsKey(bookId)) {
            return false;
        }
        return books.get(bookId) > 0;
    }

    public void take(LibraryBookId bookId) {
        int num = books.get(bookId);
        if (num - 1 == 0) {
            books.remove(bookId);
        } else {
            books.replace(bookId, num - 1);
        }
    }

    public void put(LibraryBookId bookId) {
        if (!books.containsKey(bookId)) {
            books.put(bookId, 1);
        } else {
            books.replace(bookId, books.get(bookId) + 1);
        }
    }

    public Map<LibraryBookId, Integer> getBooks() {
        return books;
    }
}
