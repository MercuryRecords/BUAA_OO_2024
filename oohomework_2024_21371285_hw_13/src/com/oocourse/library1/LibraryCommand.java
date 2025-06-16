package com.oocourse.library1;

import java.time.LocalDate;

public class LibraryCommand<T> {
    private final LocalDate date;
    private final T cmd;

    public LibraryCommand(LocalDate date, T cmd) {
        this.date = date;
        this.cmd = cmd;
    }

    /**
     * 获取请求日期
     *
     * @return 请求日期
     */
    public LocalDate getDate() {
        return date;
    }

    /**
     * 获取请求命令详情
     *
     * @return 请求命令
     */
    public T getCmd() {
        return cmd;
    }

    @Override
    public String toString() {
        return "[" + LibrarySystem.DTF.format(date) + "] " + cmd;
    }
}
