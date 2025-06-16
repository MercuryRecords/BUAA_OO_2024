package com.oocourse.library3.annotation;

import java.lang.annotation.Documented;
import java.lang.annotation.ElementType;
import java.lang.annotation.Repeatable;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * SendMessage 用于顺序图中消息发送。
 * 第一个元素 {@code from} 作为消息发送者；
 * 第二个元素 {@code to} 作为消息接受者。
 * <br><br>
 * 示例如下：<br>
 * <pre><code>
 * {@literal @}SendMessage(from = "Sender1", to = "Receiver1")
 * {@literal @}SendMessage(from = "Sender1", to = "Receiver2")
 *  void sending() {
 *      // some code here...
 *  }
 * </code></pre>
 * 该示例表示了{@code sending}方法会从{@code Sender1}发送消息
 * 给{@code Receiver1}和/或{@code Receiver2}。
 */
@Documented
@Repeatable(SendMessages.class)
@Target(ElementType.METHOD)
@Retention(RetentionPolicy.RUNTIME)
public @interface SendMessage {
    String from();

    String to();
}
