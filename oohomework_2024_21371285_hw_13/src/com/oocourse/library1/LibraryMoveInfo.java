package com.oocourse.library1;

public class LibraryMoveInfo {
    private final LibraryBookId bookId;
    private final String from;
    private final String to;
    private final String reserveFor;

    /**
     * 图书移动信息（终点不为预约处）
     */
    public LibraryMoveInfo(LibraryBookId bookId, String from, String to) {
        this.bookId = bookId;
        this.from = from;
        this.to = to;
        this.reserveFor = null;
    }

    /**
     * 图书移动信息（终点为预约处）
     */
    public LibraryMoveInfo(LibraryBookId bookId, String from, String to, String reserveFor) {
        this.bookId = bookId;
        this.from = from;
        this.to = to;
        this.reserveFor = reserveFor;
    }

    /**
     * 获取 Book Id
     *
     * @return Book Id
     */
    public LibraryBookId getBookId() {
        return bookId;
    }

    /**
     * 获取转运起点
     *
     * @return 转运起点
     */
    public String getFrom() {
        return from;
    }

    /**
     * 获取转运终点
     *
     * @return 转运终点
     */
    public String getTo() {
        return to;
    }

    /**
     * 获取预留者学号
     *
     * @return 预留者学号（没有返回 null）
     */
    public String getReserveFor() {
        return reserveFor;
    }

    @Override
    public String toString() {
        String str = "move " + bookId + " from " + from + " to " + to;
        if (reserveFor != null) {
            str += " for " + reserveFor;
        }
        return str;
    }
}
