package com.oocourse.library2;

import java.time.LocalDate;
import java.util.Objects;

public class LibraryCloseCmd extends LibraryCommand {
    public LibraryCloseCmd(LocalDate date) {
        super(date);
    }

    /**
     * 判断 obj 是否为 "CLOSE" 或任何 LibraryCloseCmd 实例
     *
     * @param obj 欲判断的其他对象
     * @return obj 是否为 "CLOSE" 或任何 LibraryCloseCmd 实例
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj) { return true; }
        if (obj == null) { return false; }
        if (obj.equals("CLOSE")) { return true; }
        return obj instanceof LibraryCloseCmd;
    }

    @Override
    public int hashCode() {
        return Objects.hashCode("CLOSE");
    }

    @Override
    public String getCommandString() {
        return "CLOSE";
    }
}
