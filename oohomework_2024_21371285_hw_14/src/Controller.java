import com.oocourse.library2.LibraryCommand;
import com.oocourse.library2.LibraryReqCmd;
import com.oocourse.library2.LibraryScanner;
import com.oocourse.library2.LibrarySystem;

public class Controller extends Thread {
    private final LibraryScanner scanner = LibrarySystem.SCANNER;
    public static final Bookstore BOOKSHELF = new Bookstore(LibrarySystem.SCANNER.getInventory());
    public static final Bookstore CCSTORE = new Bookstore();
    private final Circulation circulation;
    private final Reservation reservation;
    private final Cart cart;

    public Controller() {
        Bookstore circulationStore = new Bookstore();
        Bookstore reservationStore = new Bookstore();
        circulation = new Circulation(circulationStore);
        reservation = new Reservation(reservationStore);
        cart = new Cart(circulation, reservation);
    }

    @Override
    public void run() {
        LibraryCommand cmd;
        while (true) {
            cmd = scanner.nextCommand();
            if (cmd == null) {
                break;
            } else if (cmd instanceof LibraryReqCmd) {
                // LibraryRequest
                LibraryReqCmd reqCmd = (LibraryReqCmd) cmd;
                switch (reqCmd.getType()) {
                    case BORROWED:
                        circulation.handleBorrow(reqCmd);
                        break;
                    case RETURNED:
                        circulation.handleReturn(reqCmd);
                        break;
                    case ORDERED:
                        reservation.handleOrder(reqCmd);
                        break;
                    case PICKED:
                        reservation.handlePick(reqCmd);
                        break;
                    case QUERIED:
                        if (reqCmd.getBookId().isFormal()) {
                            BOOKSHELF.query(reqCmd);
                        } else {
                            CCSTORE.query(reqCmd);
                        }
                        break;
                    case RENEWED:
                        Facebook.INSTANCE.handleRenew(reqCmd);
                        break;
                    case DONATED:
                        CCSTORE.put(reqCmd.getBookId());
                        LibrarySystem.PRINTER.accept(reqCmd);
                        break;
                    default:
                        System.out.println("wrong req type");
                        break;
                }
            } else {
                cart.sort(cmd.getCommandString(), cmd.getDate());
            }
        }
    }
}
