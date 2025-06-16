package com.oocourse.library3;

import java.time.LocalDate;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * LibraryScanner 和 LibraryPrinter 的默认实现
 */
class LibraryDefault {
    static class Scanner implements LibraryScanner {
        private static final boolean PRINT_STDERR = false;
        private final java.util.Scanner scanner = new java.util.Scanner(System.in);

        @Override
        public Map<LibraryBookId, Integer> getInventory() {
            Map<LibraryBookId, Integer> inventory = new HashMap<>();
            int size = Integer.parseInt(scanner.nextLine());
            if (PRINT_STDERR) { System.err.println(size); }
            for (int i = 0; i < size; i++) {
                String line = scanner.nextLine();
                if (PRINT_STDERR) { System.err.println(line); }
                String[] array = line.split(" ");
                inventory.put(LibraryBookId.parse(array[0]), Integer.parseInt(array[1]));
            }
            return inventory;
        }

        @Override
        public LibraryCommand nextCommand() {
            if (!scanner.hasNextLine()) { return null; }
            String dateString = scanner.next();
            LocalDate date = LocalDate.parse(dateString.substring(1, dateString.length() - 1), LibrarySystem.DTF);
            String command = scanner.nextLine().trim();
            if (PRINT_STDERR) { System.err.println(dateString + " " + command); }
            switch (command) {
                case "OPEN":
                    return new LibraryOpenCmd(date);
                case "CLOSE":
                    return new LibraryCloseCmd(date);
                default:
                    if (command.endsWith("queried credit score")) {
                        return new LibraryQcsCmd(date, command.split(" ")[0]);
                    } else {
                        return new LibraryReqCmd(date, LibraryRequest.parse(command));
                    }
            }
        }
    }

    static class Printer implements LibraryPrinter {
        @Override
        public void reject(LibraryCommand command) {
            System.out.println(command.getDateString() + " [reject] " + command.getCommandString());
        }

        @Override
        public void reject(LibraryCommand command, String additionalInfo) {
            System.out.println(command.getDateString() + " [reject] "
                    + command.getCommandString() + " " + additionalInfo);
        }

        @Override
        public void accept(LibraryCommand command) {
            System.out.println(command.getDateString() + " [accept] " + command.getCommandString());
        }

        @Override
        public void accept(LibraryCommand command, String additionalInfo) {
            System.out.println(command.getDateString() + " [accept] "
                    + command.getCommandString() + " " + additionalInfo);
        }

        @Override
        public void info(LocalDate date, LibraryBookId bookId, int count) {
            System.out.println("[" + LibrarySystem.DTF.format(date) + "] " + bookId + " " + count);
        }

        @Override
        public void info(LocalDate date, String studentId, int credit) {
            System.out.println("[" + LibrarySystem.DTF.format(date) + "] " + studentId + " " + credit);
        }

        @Override
        public void move(LocalDate date, List<LibraryMoveInfo> info) {
            System.out.println(info.size());
            for (LibraryMoveInfo item : info) {
                System.out.println("[" + LibrarySystem.DTF.format(date) + "] " + item);
            }
        }
    }
}
