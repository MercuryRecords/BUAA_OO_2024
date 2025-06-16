package com.oocourse.spec3.main;

public interface Tag {

    /*@ public instance model int id;
      @ public instance model non_null Person[] persons;
      @*/

    /*@ invariant persons!= null &&
      @  (\forall int i,j; 0 <= i && i < j && j < persons.length;
      @   !persons[i].equals(persons[j]));
      @*/

    //@ ensures \result == id;
    public /*@ pure @*/ int getId();

    /*@ public normal_behavior
      @ requires obj != null && obj instanceof Tag;
      @ assignable \nothing;
      @ ensures \result == (((Tag) obj).getId() == id);
      @ also
      @ public normal_behavior
      @ requires obj == null || !(obj instanceof Tag);
      @ assignable \nothing;
      @ ensures \result == false;
      @*/
    public /*@ pure @*/ boolean equals(Object obj);

    /*@ public normal_behavior
      @ requires !hasPerson(person);
      @ assignable persons;
      @ ensures hasPerson(person);
      @*/
    public /*@ safe @*/ void addPerson(/*@ non_null @*/Person person);

    //@ ensures \result == (\exists int i; 0 <= i && i < persons.length; persons[i].equals(person));
    public /*@ pure @*/ boolean hasPerson(Person person);

    /*@ ensures \result == (\sum int i; 0 <= i && i < persons.length; 
      @          (\sum int j; 0 <= j && j < persons.length && 
      @           persons[i].isLinked(persons[j]); persons[i].queryValue(persons[j])));
      @*/
    public /*@ pure @*/ int getValueSum();

    /*@ ensures \result == (persons.length == 0? 0:
      @          ((\sum int i; 0 <= i && i < persons.length; persons[i].getAge()) / persons.length));
      @*/
    public /*@ pure @*/ int getAgeMean();

    /*@ ensures \result == (persons.length == 0? 0 : ((\sum int i; 0 <= i && i < persons.length; 
      @          (persons[i].getAge() - getAgeMean()) * (persons[i].getAge() - getAgeMean())) / 
      @           persons.length));
      @*/
    public /*@ pure @*/ int getAgeVar();

    /*@ public normal_behavior
      @ requires hasPerson(person);
      @ assignable persons;
      @ ensures !hasPerson(person);
      @*/
    public /*@ safe @*/ void delPerson(/*@ non_null @*/Person person);

    //@ ensures \result == persons.length;
    public /*@ pure @*/ int getSize();
}