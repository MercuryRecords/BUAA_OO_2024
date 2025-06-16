package com.oocourse.spec3.main;

public interface Message {
    /*@ public instance model int id;
      @ public instance model int socialValue;
      @ public instance model int type;
      @ public instance model non_null Person person1;
      @ public instance model nullable Person person2;
      @ public instance model nullable Tag tag;
      @*/

    // invariant person1!= null && !person1.equals(person2);

    //@ ensures \result == type;
    public /*@ pure @*/ int getType();

    //@ ensures \result == id;
    public /*@ pure @*/ int getId();

    //@ ensures \result == socialValue;
    public /*@ pure @*/ int getSocialValue();

    //@ ensures \result == person1;
    public /*@ pure @*/ Person getPerson1();

    /*@ requires person2 != null;
      @ ensures \result == person2;
      @*/
    public /*@ pure @*/ Person getPerson2();

    /*@ requires tag != null;
      @ ensures \result == tag;
      @*/
    public /*@ pure @*/ Tag getTag();

    /*@ public normal_behavior
      @ requires obj != null && obj instanceof Message;
      @ assignable \nothing;
      @ ensures \result == (((Message) obj).getId() == id);
      @ also
      @ public normal_behavior
      @ requires obj == null || !(obj instanceof Message);
      @ assignable \nothing;
      @ ensures \result == false;
      @*/
    public /*@ pure @*/ boolean equals(Object obj);
}
