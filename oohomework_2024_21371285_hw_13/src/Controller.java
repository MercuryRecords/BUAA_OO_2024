import com.oocourse.library1.LibraryCommand;
import com.oocourse.library1.LibraryRequest;
import com.oocourse.library1.LibraryScanner;
import com.oocourse.library1.LibrarySystem;

import java.time.LocalDate;

public class Controller extends Thread {
    private final LibraryScanner scanner = LibrarySystem.SCANNER;
    private final Bookstore bookshelf;
    private final Circulation circulation;
    private final Reservation reservation;
    private final Cart cart;

    public Controller() {
        bookshelf = new Bookstore(scanner.getInventory());
        Bookstore circulationStore = new Bookstore();
        Bookstore reservationStore = new Bookstore();
        circulation = new Circulation(bookshelf, circulationStore);
        reservation = new Reservation(bookshelf, reservationStore);
        cart = new Cart(bookshelf, circulationStore, reservation);
    }

    @Override
    public void run() {
        LibraryCommand<?> cmd;
        while (true) {
            cmd = scanner.nextCommand();
            if (cmd == null) {
                break;
            } else if (cmd.getCmd() instanceof LibraryRequest) {
                // LibraryRequest
                LibraryRequest req = (LibraryRequest) cmd.getCmd();
                LocalDate date = cmd.getDate();
                switch (req.getType()) {
                    case BORROWED:
                        circulation.handleBorrow(date, req);
                        break;
                    case RETURNED:
                        circulation.handleReturn(date, req);
                        break;
                    case ORDERED:
                        reservation.handleOrder(date, req);
                        break;
                    case PICKED:
                        reservation.handlePick(date, req);
                        break;
                    case QUERIED:
                        bookshelf.query(date, req);
                        break;
                    default:
                        System.out.println("wrong req type");
                        break;
                }
            } else {
                cart.sort((String) cmd.getCmd(), cmd.getDate());
            }
        }
    }
}
