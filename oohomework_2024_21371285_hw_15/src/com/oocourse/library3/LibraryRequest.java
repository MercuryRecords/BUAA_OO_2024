package com.oocourse.library3;

import java.util.Objects;

public class LibraryRequest {
    public LibraryRequest(Type type, String studentId, LibraryBookId bookId) {
        this.type = type;
        this.studentId = studentId;
        this.bookId = bookId;
    }

    /**
     * 解析给定字符串并构造 LibraryRequest
     *
     * @param fromString 格式为 "&lt;学号&gt; &lt;操作&gt; &lt;类别号-序列号&gt;"
     * @return LibraryRequest
     * @throws RuntimeException 若字符串无法解析
     */
    static LibraryRequest parse(String fromString) {
        String[] parts = fromString.split(" ");
        try {
            return new LibraryRequest(
                    Type.parse(parts[1]),
                    parts[0],
                    LibraryBookId.parse(parts[2])
            );
        } catch (ArrayIndexOutOfBoundsException | IllegalArgumentException e) {
            throw new RuntimeException("Invalid request: " + fromString);
        }
    }

    public enum Type {
        QUERIED, BORROWED, ORDERED, RETURNED, PICKED, RENEWED, DONATED;

        @Override
        public String toString() {
            return this.name().toLowerCase();
        }

        static Type parse(String string) {
            return Type.valueOf(string.toUpperCase());
        }
    }

    private final Type type;
    private final String studentId;
    private final LibraryBookId bookId;

    /**
     * 获取请求类型
     *
     * @return 请求类型
     */
    public Type getType() {
        return type;
    }

    /**
     * 获取请求用户学号
     *
     * @return 请求用户学号
     */
    public String getStudentId() {
        return studentId;
    }

    /**
     * 获取请求书籍类别号-序列号
     *
     * @return 请求书籍类别号-序列号
     */
    public LibraryBookId getBookId() {
        return bookId;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) { return true; }
        if (!(o instanceof LibraryRequest)) { return false; }
        LibraryRequest other = (LibraryRequest) o;
        return type == other.type && Objects.equals(studentId, other.studentId) && Objects.equals(bookId, other.bookId);
    }

    @Override
    public int hashCode() {
        return Objects.hash(type, studentId, bookId);
    }

    @Override
    public String toString() {
        return studentId + " " + type.toString().toLowerCase() + " " + bookId;
    }
}
