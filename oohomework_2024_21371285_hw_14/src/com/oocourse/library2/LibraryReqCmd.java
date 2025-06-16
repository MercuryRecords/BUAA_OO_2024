package com.oocourse.library2;

import java.time.LocalDate;
import java.util.Objects;

public class LibraryReqCmd extends LibraryCommand {
    private final LibraryRequest request;

    public LibraryReqCmd(LocalDate date, LibraryRequest request) {
        super(date);
        this.request = request;
    }

    /**
     * 获取请求信息
     *
     * @return 请求信息
     */
    public LibraryRequest getRequest() {
        return request;
    }

    /**
     * 获取请求类型
     *
     * @return 请求类型
     */
    public LibraryRequest.Type getType() {
        return request.getType();
    }

    /**
     * 获取请求用户学号
     *
     * @return 请求用户学号
     */
    public String getStudentId() {
        return request.getStudentId();
    }

    /**
     * 获取请求书籍类别号-序列号
     *
     * @return 请求书籍类别号-序列号
     */
    public LibraryBookId getBookId() {
        return request.getBookId();
    }

    /**
     * 判断 Request 是否相等。注意：不会判断日期是否相等！
     *
     * @param o 其他对象
     * @return 判断两个对象是否均为<code>LibraryReqCmd</code>并且其<code>getRequest()</code>完全一致
     */
    @Override
    public boolean equals(Object o) {
        if (this == o) { return true; }
        if (!(o instanceof LibraryReqCmd)) { return false; }
        LibraryReqCmd other = (LibraryReqCmd) o;
        return Objects.equals(request, other.request);
    }

    @Override
    public int hashCode() {
        return Objects.hashCode(request);
    }

    @Override
    public String getCommandString() {
        return request.toString();
    }
}
