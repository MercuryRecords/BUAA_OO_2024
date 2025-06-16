import com.oocourse.library1.LibraryBookId;
import com.oocourse.library1.LibraryMoveInfo;
import com.oocourse.library1.LibrarySystem;

import java.time.LocalDate;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;

public class Cart {
    private final Bookstore bookshelf;
    private final Bookstore circulationStore;
    private final Reservation reservation;

    public Cart(Bookstore bookshelf, Bookstore circulationStore, Reservation reservation) {
        this.bookshelf = bookshelf;
        this.circulationStore = circulationStore;
        this.reservation = reservation;
    }

    public void sort(String type, LocalDate date) {
        LinkedList<LibraryMoveInfo> infos = new LinkedList<>();
        if (type.equals("OPEN")) {
            // 借还处退回
            Map<LibraryBookId, Integer> from = circulationStore.getBooks();
            Iterator<Map.Entry<LibraryBookId, Integer>> it = from.entrySet().iterator();
            while (it.hasNext()) {
                Map.Entry<LibraryBookId, Integer> entry = it.next();
                int cnt = entry.getValue();
                LibraryBookId name = entry.getKey();
                while (cnt-- > 0) {
                    bookshelf.put(name);
                    infos.add(new LibraryMoveInfo(name, "bro", "bs"));
                }
                it.remove();
            }
            // 过期预约取消（我勒个次日才能整理啊）
            infos.addAll(reservation.returnExpired(date.minusDays(4)));
            // 运送预约书籍
            infos.addAll(reservation.prepareOrdered(date));
        }
        LibrarySystem.PRINTER.move(date, infos);
    }
}
