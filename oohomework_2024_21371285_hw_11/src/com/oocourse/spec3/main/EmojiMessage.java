package com.oocourse.spec3.main;

public interface EmojiMessage extends Message {
    //@ public instance model int emojiId;

    //@ public invariant socialValue == emojiId;

    //@ ensures \result == emojiId;
    public /*@ pure @*/ int getEmojiId();
}
