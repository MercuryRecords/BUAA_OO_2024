package com.oocourse.spec3.main;

import java.util.List;

public interface Person {

    /*@ public instance model int id;
      @ public instance model non_null String name;
      @ public instance model int age;
      @ public instance model non_null Person[] acquaintance;
      @ public instance model non_null int[] value;
      @ public instance model non_null Tag[] tags;
      @ public instance model int money;
      @ public instance model int socialValue;
      @ public instance model non_null Message[] messages;
      @*/


    /*@ invariant acquaintance != null && value != null && tags != null && messages != null && acquaintance.length == value.length &&
      @  (\forall int i,j; 0 <= i && i < j && j < acquaintance.length;
      @   !acquaintance[i].equals(acquaintance[j])) &&
      @  (\forall int i,j; 0 <= i && i < j && j < tags.length;
      @   !tags[i].equals(tags[j])) && 
      @   (\forall int i,j; 0 <= i && i < j && j < messages.length;
      @   !messages[i].equals(messages[j]));
      @*/

    

    //@ ensures \result == id;
    public /*@ pure @*/ int getId();

    //@ ensures \result == name;
    public /*@ pure @*/ String getName();

    //@ ensures \result == age;
    public /*@ pure @*/ int getAge();

    //@ ensures \result == (\exists int i; 0 <= i && i < tags.length; tags[i].getId() == id);
    public /*@ pure @*/ boolean containsTag(int id);

    /*@ public normal_behavior
      @ requires containsTag(id);
      @ ensures (\exists int i; 0 <= i && i < tags.length; tags[i].getId() == id &&
      @         \result == tags[i]);
      @ also
      @ public normal_behavior
      @ requires !containsTag(id);
      @ ensures \result == null;
      @*/
    public /*@ pure @*/ Tag getTag(int id);

    /*@ public normal_behavior
      @ requires !containsTag(tag.getId());
      @ assignable tags;
      @ ensures containsTag(tag.getId());
      @*/
    public /*@ safe @*/ void addTag(/*@ non_null @*/Tag tag);

    /*@ public normal_behavior
      @ requires containsTag(id);
      @ assignable tags;
      @ ensures !containsTag(id);
      @*/
    public /*@ safe @*/ void delTag(int id);

    /*@ public normal_behavior
      @ requires obj != null && obj instanceof Person;
      @ assignable \nothing;
      @ ensures \result == (((Person) obj).getId() == id);
      @ also
      @ public normal_behavior
      @ requires obj == null || !(obj instanceof Person);
      @ assignable \nothing;
      @ ensures \result == false;
      @*/
    public /*@ pure @*/ boolean equals(Object obj);

    /*@ public normal_behavior
      @ assignable \nothing;
      @ ensures \result == (\exists int i; 0 <= i && i < acquaintance.length; 
      @                     acquaintance[i].getId() == person.getId()) || person.getId() == id;
      @*/
    public /*@ pure @*/ boolean isLinked(Person person);

    /*@ public normal_behavior
      @ requires (\exists int i; 0 <= i && i < acquaintance.length; 
      @          acquaintance[i].getId() == person.getId());
      @ assignable \nothing;
      @ ensures (\exists int i; 0 <= i && i < acquaintance.length;
      @         acquaintance[i].getId() == person.getId() && \result == value[i]);
      @ also
      @ public normal_behavior
      @ requires (\forall int i; 0 <= i && i < acquaintance.length; 
      @          acquaintance[i].getId() != person.getId());
      @ ensures \result == 0;
      @*/
    public /*@ pure @*/ int queryValue(Person person);

    /*@ public normal_behavior
      @ assignable socialValue;
      @ ensures socialValue == \old(socialValue) + num;
      @*/
    public void addSocialValue(int num);

    //@ ensures \result == socialValue;
    public /*@ pure @*/ int getSocialValue();

    /*@ ensures (\result.size() == messages.length) && 
      @           (\forall int i; 0 <= i && i < messages.length; 
      @             messages[i] == \result.get(i));
      @*/
    public /*@ pure @*/ List<Message> getMessages();

    /*@ public normal_behavior
      @ assignable \nothing;
      @ ensures (\forall int i; 0 <= i && i < messages.length && i <= 4;
      @           \result.contains(messages[i]) && \result.get(i) == messages[i]);
      @ ensures \result.size() == ((messages.length < 5)? messages.length: 5);
     */
    public /*@ pure @*/ List<Message> getReceivedMessages();

    /*@ public normal_behavior
      @ assignable money;
      @ ensures money == \old(money) + num;
      @*/
    public void addMoney(int num);

    //@ ensures \result == money;
    public /*@ pure @*/ int getMoney();

}
