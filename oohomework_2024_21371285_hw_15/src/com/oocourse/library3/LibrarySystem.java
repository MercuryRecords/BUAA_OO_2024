package com.oocourse.library3;

import java.time.format.DateTimeFormatter;

public class LibrarySystem {
    public static final LibrarySystem INSTANCE = new LibrarySystem(
            new LibraryDefault.Scanner(), new LibraryDefault.Printer());
    public static final LibraryScanner SCANNER = INSTANCE.scanner;
    public static final LibraryPrinter PRINTER = INSTANCE.printer;

    public static final DateTimeFormatter DTF = DateTimeFormatter.ofPattern("yyyy-MM-dd");

    private final LibraryScanner scanner;
    private final LibraryPrinter printer;

    private LibrarySystem(LibraryScanner scanner, LibraryPrinter printer) {
        this.scanner = scanner;
        this.printer = printer;
    }
}
