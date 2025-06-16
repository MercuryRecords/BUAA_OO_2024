package com.oocourse.library1;

import java.time.LocalDate;
import java.util.Arrays;
import java.util.Map;
import java.util.List;

public interface LibraryPrinter {
    /**
     * 拒绝某条请求指令
     *
     * @param date    指令执行的日期
     * @param request 请求指令
     */
    void reject(LocalDate date, LibraryRequest request);

    /**
     * 拒绝某条请求指令
     *
     * @param command 请求指令
     */
    default void reject(LibraryCommand<?> command) {
        reject(command.getDate(), (LibraryRequest) command.getCmd());
    }

    /**
     * 接受某条请求指令
     *
     * @param date    指令执行的日期
     * @param request 请求指令
     */
    void accept(LocalDate date, LibraryRequest request);

    /**
     * 接受某条请求指令
     *
     * @param command 请求指令
     */
    default void accept(LibraryCommand<?> command) {
        accept(command.getDate(), (LibraryRequest) command.getCmd());
    }

    /**
     * 打印查询到的库存信息
     *
     * @param date   指令执行的日期
     * @param bookId 查询的书籍编号
     * @param count  对应的库存数量
     */
    void info(LocalDate date, LibraryBookId bookId, int count);

    /**
     * 打印查询到的库存信息
     *
     * @param date  指令执行的日期
     * @param entry 一条库存信息
     */
    default void info(LocalDate date, Map.Entry<LibraryBookId, Integer> entry) {
        info(date, entry.getKey(), entry.getValue());
    }

    /**
     * 打印查询到的库存信息
     *
     * @param command 请求指令
     * @param count   对应的库存数量
     */
    default void info(LibraryCommand<?> command, int count) {
        LibraryRequest req = (LibraryRequest) command.getCmd();
        info(command.getDate(), req.getBookId(), count);
    }

    /**
     * 打印图书移动信息
     *
     * @param date 指令执行的日期
     * @param info 移动图书信息序列
     */
    void move(LocalDate date, List<LibraryMoveInfo> info);

    /**
     * 打印图书移动信息
     *
     * @param date 指令执行的日期
     * @param info 移动图书信息序列
     */
    default void move(LocalDate date, LibraryMoveInfo... info) {
        move(date, Arrays.asList(info));
    }
}
