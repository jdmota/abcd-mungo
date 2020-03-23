package org.checkerframework.checker.mungo.qualifiers;

import org.checkerframework.framework.qual.SubtypeOf;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;
import java.util.List;

@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.TYPE_USE, ElementType.TYPE_PARAMETER})
@SubtypeOf(MungoUnknown.class)
public @interface MungoInfo {
  String file();

  boolean allStates() default true;

  String[] states() default {};
}