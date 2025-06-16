package com.oocourse.library3;

import java.time.LocalDate;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

public interface LibraryPrinter {
    /**
     * 拒绝某条请求指令<br>
     * 输出形式为<code>[YYYY-mm-dd] [reject] &lt;学号&gt; type &lt;类别号-序列号&gt;</code>
     *
     * @param date    指令执行的日期
     * @param request 请求指令
     * @see LibraryPrinter#reject(LibraryCommand)
     * @see LibraryPrinter#reject(LibraryCommand, String)
     * @deprecated 建议使用参数为<code>LibraryCommand</code>的版本
     */
    @Deprecated
    default void reject(LocalDate date, LibraryRequest request) {
        reject(new LibraryReqCmd(date, request));
    }

    /**
     * 拒绝某条请求指令（不会输出的额外信息）<br>
     * 输出形式为<code>[YYYY-mm-dd] [reject] &lt;学号&gt; type &lt;类别号-序列号&gt;</code>
     *
     * @param command 请求指令
     * @see LibraryPrinter#reject(LibraryCommand, String)
     */
    void reject(LibraryCommand command);

    /**
     * 拒绝某条请求指令（并输出的额外信息）<br>
     * 输出形式为<code>[YYYY-mm-dd] [reject] &lt;学号&gt; type &lt;类别号-序列号&gt; additionalInfo</code><br>
     * 需注意<code>additionalInfo</code>和序列号之间已经有一个空格
     *
     * @param command        请求指令
     * @param additionalInfo 需要输出的额外信息
     */
    void reject(LibraryCommand command, String additionalInfo);

    /**
     * 接受某条请求指令<br>
     * 输出形式为<code>[YYYY-mm-dd] [accept] &lt;学号&gt; type &lt;类别号-序列号&gt;</code>
     *
     * @param date    指令执行的日期
     * @param request 请求指令
     * @see LibraryPrinter#accept(LibraryCommand)
     * @see LibraryPrinter#accept(LibraryCommand, String)
     * @deprecated 建议使用参数为<code>LibraryCommand</code>的版本
     */
    @Deprecated
    default void accept(LocalDate date, LibraryRequest request) {
        accept(new LibraryReqCmd(date, request));
    }

    /**
     * 接受某条请求指令（不会输出的额外信息）<br>
     * 输出形式为<code>[YYYY-mm-dd] [accept] &lt;学号&gt; type &lt;类别号-序列号&gt;</code>
     *
     * @param command 请求指令
     * @see LibraryPrinter#accept(LibraryCommand, String)
     */
    void accept(LibraryCommand command);

    /**
     * 接受某条请求指令（并输出的额外信息）<br>
     * 输出形式为<code>[YYYY-mm-dd] [accept] &lt;学号&gt; type &lt;类别号-序列号&gt; additionalInfo</code><br>
     * 需注意<code>additionalInfo</code>和序列号之间已经有一个空格
     *
     * @param command        请求指令
     * @param additionalInfo 需要输出的额外信息
     */
    void accept(LibraryCommand command, String additionalInfo);

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
     * 打印学生信用积分信息
     *
     * @param date      指令执行的日期
     * @param studentId 学生编号
     * @param credit    信用积分
     */
    void info(LocalDate date, String studentId, int credit);

    /**
     * 打印查询到的库存信息/学生信用积分信息
     *
     * @param command 请求指令
     * @param value   对应的库存数量/学生信用积分信息
     * @throws RuntimeException 如果给出的指令不是查询指令
     */
    default void info(LibraryCommand command, int value) {
        if (command instanceof LibraryReqCmd) {
            info(command.getDate(), ((LibraryReqCmd) command).getBookId(), value);
        } else if (command instanceof LibraryQcsCmd) {
            info(command.getDate(), ((LibraryQcsCmd) command).getStudentId(), value);
        } else {
            throw new RuntimeException("Unsupported command: " + command);
        }
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
