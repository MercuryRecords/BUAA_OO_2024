import com.oocourse.library3.LibraryBookId;
import com.oocourse.library3.LibraryMoveInfo;
import com.oocourse.library3.LibrarySystem;

import java.time.LocalDate;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;

public class Cart {
    private final Bookstore bookshelf = Controller.BOOKSHELF;
    private final Bookstore crossingCornerStore = Controller.CCSTORE;
    private final Circulation circulation;
    private final Reservation reservation;

    public Cart(Circulation circulation, Reservation reservation) {
        this.circulation = circulation;
        this.reservation = reservation;
    }

    public void sort(String type, LocalDate date) {
        LinkedList<LibraryMoveInfo> infos = new LinkedList<>();
        if (type.equals("OPEN")) {
            Facebook.INSTANCE.recordOverdue(date);
            reservation.recordExpired(date);
            // 借还处退回
            Map<LibraryBookId, Integer> from = circulation.getBooks();
            Iterator<Map.Entry<LibraryBookId, Integer>> it = from.entrySet().iterator();
            while (it.hasNext()) {
                Map.Entry<LibraryBookId, Integer> entry = it.next();
                int cnt = entry.getValue();
                LibraryBookId name = entry.getKey();
                if (!name.isFormal() && circulation.toUpgrade(name)) {
                    while (cnt-- > 0) {
                        Facebook.INSTANCE.addCreditScore(name);
                        bookshelf.put(name.toFormal());
                        infos.add(new LibraryMoveInfo(name, "bro", "bs"));
                    }
                } else if (!name.isFormal()) {
                    while (cnt-- > 0) {
                        crossingCornerStore.put(name);
                        infos.add(new LibraryMoveInfo(name, "bro", "bdc"));
                    }
                } else {
                    while (cnt-- > 0) {
                        bookshelf.put(name);
                        infos.add(new LibraryMoveInfo(name, "bro", "bs"));
                    }
                }
                it.remove();
            }
            // 过期预约取消（我勒个次日才能整理啊）
            infos.addAll(reservation.returnExpired(date.minusDays(4)));
            // 运送预约书籍
            infos.addAll(reservation.prepareOrdered(date));
        } else {
            Facebook.INSTANCE.recordOverdue(date.plusDays(1));
            reservation.recordExpired(date.plusDays(1));
        }
        LibrarySystem.PRINTER.move(date, infos);
    }
}
