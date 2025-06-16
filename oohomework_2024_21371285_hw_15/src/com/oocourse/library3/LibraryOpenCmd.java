package com.oocourse.library3;

import java.time.LocalDate;
import java.util.Objects;

public class LibraryOpenCmd extends LibraryCommand {
    public LibraryOpenCmd(LocalDate date) {
        super(date);
    }

    /**
     * 判断 obj 是否为 "OPEN" 或任何 LibraryOpenCmd 实例
     *
     * @param obj 欲判断的其他对象
     * @return obj 是否为 "OPEN" 或任何 LibraryOpenCmd 实例
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj) { return true; }
        if (obj == null) { return false; }
        if (obj.equals("OPEN")) { return true; }
        return obj instanceof LibraryOpenCmd;
    }

    @Override
    public int hashCode() {
        return Objects.hashCode("OPEN");
    }

    @Override
    public String getCommandString() {
        return "OPEN";
    }
}
