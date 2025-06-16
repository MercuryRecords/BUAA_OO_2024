package com.oocourse.library1;

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
     * 泛型参数<code>?</code>应为<code>String</code>或者<code>LibraryRequest</code>。
     *
     * @return 下一条图书馆指令，输入结束时返回 null
     */
    LibraryCommand<?> nextCommand();
}
