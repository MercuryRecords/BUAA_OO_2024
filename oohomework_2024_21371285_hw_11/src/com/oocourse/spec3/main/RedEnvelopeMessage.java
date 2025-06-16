package com.oocourse.spec3.main;

public interface RedEnvelopeMessage extends Message {
    //@ public instance model int money;

    //@ public invariant socialValue == money * 5;

    //@ ensures \result == money;
    public /*@ pure @*/ int getMoney();
}
