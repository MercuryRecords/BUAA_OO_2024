package com.oocourse.library3.annotation;

import java.lang.annotation.Documented;
import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * 用来存储 Trigger 数组。请不要直接使用。请使用{@code Trigger}。
 * @see Trigger
 */
@Documented
@Target(ElementType.METHOD)
@Retention(RetentionPolicy.RUNTIME)
public @interface Triggers {
    Trigger[] value();
}
