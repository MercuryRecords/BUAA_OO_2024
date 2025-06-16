package com.oocourse.library2;

import java.util.Map;

public interface LibraryScanner {
    /**
     * 获取图书馆库存。应该仅在图书馆系统启动时调用一次。
     *
     * @return 一个书籍编号到数量的映射
     */
    Map<LibraryBookId, Integer> getInventory();

    /**
     * 获取下一条图书馆指令。
     * 返回值为 LibraryCommand，可能是下列三种中的一种：
     * <ul>
     * <li>LibraryOpenCmd: OPEN 指令</li>
     * <li>LibraryCloseCmd: CLOSE 指令</li>
     * <li>LibraryReqCmd: 请求指令</li>
     * </ul>
     *
     * @return 下一条图书馆指令，输入结束时返回 null
     * @see LibraryOpenCmd
     * @see LibraryCloseCmd
     * @see LibraryReqCmd
     */
    LibraryCommand nextCommand();
}
