package com.oocourse.library2;

import java.time.LocalDate;

public class LibraryCommand {
    private final LocalDate date;

    public LibraryCommand(LocalDate date) {
        this.date = date;
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
     * @deprecated 该方法只会返回自身
     */
    @Deprecated
    public LibraryCommand getCmd() {
        return this;
    }

    /**
     * 获取格式化日期字符串
     *
     * @return 格式化日期字符串
     */
    public String getDateString() {
        return "[" + LibrarySystem.DTF.format(date) + "]";
    }

    /**
     * 返回指令详细信息对应的字符串
     *
     * @return （不含日期的）指令详细字符串
     */
    public String getCommandString() {
        return "";
    }

    @Override
    public String toString() {
        return getDateString() + " " + getCommandString();
    }
}
