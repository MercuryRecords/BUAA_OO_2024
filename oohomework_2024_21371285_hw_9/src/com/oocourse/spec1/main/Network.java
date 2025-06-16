package com.oocourse.spec1.main;

import com.oocourse.spec1.exceptions.*;

public interface Network {

    /*@ public instance model non_null Person[] persons;
      @*/

    /*@ invariant persons != null && (\forall int i,j; 0 <= i && i < j && j < persons.length; !persons[i].equals(persons[j]));*/

    //@ ensures \result == (\exists int i; 0 <= i && i < persons.length; persons[i].getId() == id);
    public /*@ pure @*/ boolean containsPerson(int id);

    /*@ public normal_behavior
      @ requires containsPerson(id);
      @ ensures (\exists int i; 0 <= i && i < persons.length; persons[i].getId() == id &&
      @         \result == persons[i]);
      @ also
      @ public normal_behavior
      @ requires !containsPerson(id);
      @ ensures \result == null;
      @*/
    public /*@ pure @*/ Person getPerson(int id);

    /*@ public normal_behavior
      @ requires !containsPerson(person.getId());
      @ assignable persons;
      @ ensures containsPerson(person.getId());
      @ also
      @ public exceptional_behavior
      @ signals (EqualPersonIdException e) containsPerson(person.getId());
      @*/
    public /*@ safe @*/ void addPerson(/*@ non_null @*/Person person) throws EqualPersonIdException;

    /*@ public normal_behavior
      @ requires containsPerson(id1) &&
      @          containsPerson(id2) &&
      @          !getPerson(id1).isLinked(getPerson(id2));
      @ assignable persons[*];
      @ ensures getPerson(id1).isLinked(getPerson(id2)) &&
      @         getPerson(id2).isLinked(getPerson(id1));
      @ ensures getPerson(id1).queryValue(getPerson(id2)) == value;
      @ ensures getPerson(id2).queryValue(getPerson(id1)) == value;
      @ also
      @ public exceptional_behavior
      @ assignable \nothing;
      @ requires !containsPerson(id1) ||
      @          !containsPerson(id2) ||
      @          getPerson(id1).isLinked(getPerson(id2));
      @ signals (PersonIdNotFoundException e) !containsPerson(id1);
      @ signals (PersonIdNotFoundException e) containsPerson(id1) &&
      @                                       !containsPerson(id2);
      @ signals (EqualRelationException e) containsPerson(id1) &&
      @                                    containsPerson(id2) &&
      @                                    getPerson(id1).isLinked(getPerson(id2));
      @*/
    public /*@ safe @*/ void addRelation(int id1, int id2, int value) throws
            PersonIdNotFoundException, EqualRelationException;

    /*@ public normal_behavior
      @ requires containsPerson(id1) &&
      @          containsPerson(id2) &&
      @          id1 != id2 &&
      @          getPerson(id1).isLinked(getPerson(id2)) &&
      @          getPerson(id1).queryValue(getPerson(id2)) + value > 0;
      @ assignable persons[*];
      @ ensures getPerson(id1).isLinked(getPerson(id2)) &&
      @         getPerson(id2).isLinked(getPerson(id1));
      @ ensures getPerson(id1).queryValue(getPerson(id2)) == \old(getPerson(id1).queryValue(getPerson(id2))) + value;
      @ ensures getPerson(id2).queryValue(getPerson(id1)) == \old(getPerson(id2).queryValue(getPerson(id1))) + value;
      @ also
      @ public normal_behavior
      @ requires containsPerson(id1) &&
      @          containsPerson(id2) &&
      @          id1 != id2 &&
      @          getPerson(id1).isLinked(getPerson(id2)) &&
      @          getPerson(id1).queryValue(getPerson(id2)) + value <= 0;
      @ assignable persons[*];
      @ ensures  !getPerson(id1).isLinked(getPerson(id2)) &&
      @          !getPerson(id2).isLinked(getPerson(id1));
      @ ensures  getPerson(id1).value.length == getPerson(id1).acquaintance.length;
      @ ensures  getPerson(id2).value.length == getPerson(id2).acquaintance.length;
      @ also
      @ public exceptional_behavior
      @ requires !containsPerson(id1) ||
      @          !containsPerson(id2) ||
      @          id1 == id2 ||
      @          !getPerson(id1).isLinked(getPerson(id2));
      @ signals (PersonIdNotFoundException e) !containsPerson(id1);
      @ signals (PersonIdNotFoundException e) containsPerson(id1) &&
      @                                       !containsPerson(id2);
      @ signals (EqualPersonIdException e) containsPerson(id1) &&
      @                                    containsPerson(id2) &&
      @                                    id1 == id2;
      @ signals (RelationNotFoundException e) containsPerson(id1) &&
      @                                       containsPerson(id2) &&
      @                                       id1 != id2 &&
      @                                       !getPerson(id1).isLinked(getPerson(id2));
      @*/
    public /*@ safe @*/ void modifyRelation(int id1, int id2, int value) throws PersonIdNotFoundException,
            EqualPersonIdException, RelationNotFoundException;


    /*@ public normal_behavior
      @ requires containsPerson(id1) &&
      @          containsPerson(id2) &&
      @          getPerson(id1).isLinked(getPerson(id2));
      @ assignable \nothing;
      @ ensures \result == getPerson(id1).queryValue(getPerson(id2));
      @ also
      @ public exceptional_behavior
      @ signals (PersonIdNotFoundException e) !containsPerson(id1);
      @ signals (PersonIdNotFoundException e) containsPerson(id1) &&
      @                                       !containsPerson(id2);
      @ signals (RelationNotFoundException e) containsPerson(id1) &&
      @                                       containsPerson(id2) &&
      @                                       !getPerson(id1).isLinked(getPerson(id2));
      @*/
    public /*@ pure @*/ int queryValue(int id1, int id2) throws
            PersonIdNotFoundException, RelationNotFoundException;


    /*@ public normal_behavior
      @ requires containsPerson(id1) &&
      @          containsPerson(id2);
      @ assignable \nothing;
      @ ensures \result == (\exists Person[] array; array.length >= 2;
      @                     array[0].equals(getPerson(id1)) &&
      @                     array[array.length - 1].equals(getPerson(id2)) &&
      @                      (\forall int i; 0 <= i && i < array.length - 1;
      @                      array[i].isLinked(array[i + 1])));
      @ also
      @ public exceptional_behavior
      @ signals (PersonIdNotFoundException e) !containsPerson(id1);
      @ signals (PersonIdNotFoundException e) containsPerson(id1) &&
      @                                       !containsPerson(id2);
      @*/
    public /*@ pure @*/ boolean isCircle(int id1, int id2) throws PersonIdNotFoundException;
    
    /*@ ensures \result ==
      @         (\sum int i; 0 <= i && i < persons.length &&
      @         (\forall int j; 0 <= j && j < i; !isCircle(persons[i].getId(), persons[j].getId()));
      @         1);
      @*/
    public /*@ pure @*/ int queryBlockSum();
    
    /*@ ensures \result ==
      @         (\sum int i; 0 <= i && i < persons.length;
      @             (\sum int j; i < j && j < persons.length;
      @                 (\sum int k; j < k && k < persons.length
      @                     && getPerson(persons[i].getId()).isLinked(getPerson(persons[j].getId()))
      @                     && getPerson(persons[j].getId()).isLinked(getPerson(persons[k].getId()))
      @                     && getPerson(persons[k].getId()).isLinked(getPerson(persons[i].getId()));
      @                     1)));
      @*/
    public /*@ pure @*/ int queryTripleSum();
    
    
}
