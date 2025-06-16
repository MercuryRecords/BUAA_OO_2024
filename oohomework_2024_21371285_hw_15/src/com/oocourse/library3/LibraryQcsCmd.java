package com.oocourse.library3;

import java.time.LocalDate;
import java.util.Objects;

/**
 * QcsCmd: Query Credit Score Command
 */
public class LibraryQcsCmd extends LibraryCommand {
    private final String studentId;

    public LibraryQcsCmd(LocalDate date, String studentId) {
        super(date);
        this.studentId = studentId;
    }

    /**
     * 获取查询学生的学号
     *
     * @return 查询学生的学号
     */
    public String getStudentId() {
        return studentId;
    }

    /**
     * 判断是否相等，注意只会判断对应学生是否一致，不会判断日期是否一致
     *
     * @param o 其他对象
     * @return 是否相等
     */
    @Override
    public boolean equals(Object o) {
        if (this == o) { return true; }
        if (!(o instanceof LibraryQcsCmd)) { return false; }
        LibraryQcsCmd other = (LibraryQcsCmd) o;
        return Objects.equals(studentId, other.studentId);
    }

    @Override
    public int hashCode() {
        return Objects.hash(LibraryRequest.Type.QUERIED, studentId);
    }

    @Override
    public String getCommandString() {
        return studentId + " queried credit score";
    }
}
