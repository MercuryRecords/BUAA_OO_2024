package com.oocourse.library2.annotation;

import java.lang.annotation.Documented;
import java.lang.annotation.ElementType;
import java.lang.annotation.Repeatable;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Trigger 触发器。
 * 第一个元素 {@code from} 作为状态转移起点，包含且只能包含一个状态；
 * 第二个元素 {@code to} 作为状态转移终点，可以包含1个或多个状态。
 * <br><br>
 * 示例如下：<br>
 * <pre><code>
 * {@literal @}Trigger(from = "S1", to = { "S2", "S3" })
 * {@literal @}Trigger(from = "S2", to = "S3")
 *  void triggerMethod() {
 *      // some code here...
 *  }
 * </code></pre>
 * 该示例表示了一个{@code triggerMethod}是一个触发器，
 * 可以将状态从S1转移到S2或S3（根据某些其他条件（guard）），
 * 也可以将状态从S2转移到S3（由于只有一个转移目标，因此可能是无条件转移）。
 */
@Documented
@Repeatable(Triggers.class)
@Target(ElementType.METHOD)
@Retention(RetentionPolicy.RUNTIME)
public @interface Trigger {
    String from();

    String[] to();
}
