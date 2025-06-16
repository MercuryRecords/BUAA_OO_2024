package com.oocourse.spec2.main;

import com.oocourse.spec2.exceptions.*;

@SuppressWarnings("CheckStyle")
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
      @ ensures  (\forall int i; 0 <= i && i < getPerson(id1).tags.length;
      @                      \old(getPerson(id1).tags[i].hasPerson(getPerson(id2))==>!getPerson(id1).tags[i].hasPerson(getPerson(id2));
      @ ensures  (\forall int i; 0 <= i && i < getPerson(id2).tags.length;
      @                      \old(getPerson(id2).tags[i].hasPerson(getPerson(id1))==>!getPerson(id2).tags[i].hasPerson(getPerson(id1));
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



    /*@ public normal_behavior
      @ requires containsPerson(personId) &&
      @          !getPerson(personId).containsTag(tag.getId());
      @ assignable getPerson(personId).tags;
      @ ensures getPerson(personId).containsTag(tag.getId());
      @ also
      @ public exceptional_behavior
      @ signals (PersonIdNotFoundException e) !containsPerson(personId);
      @ signals (EqualTagIdException e) containsPerson(personId) &&
      @                                 getPerson(personId).containsTag(tag.getId());
      @*/
    public /*@ safe @*/ void addTag(int personId,/*@ non_null @*/Tag tag) throws PersonIdNotFoundException,EqualTagIdException;

    /*@ public normal_behavior
      @ requires containsPerson(personId1) &&
      @          containsPerson(personId2) &&
      @          personId1!=personId2      &&
      @          getPerson(personId2).isLinked(getPerson(personId1)) &&
      @          getPerson(personId2).containsTag(tagId) &&
      @          !getPerson(personId2).getTag(tagId).hasPerson(getPerson(personId1)) &&
      @          getPerson(personId2).getTag(tagId).persons.length <= 1111;
      @ assignable getPerson(personId2).getTag(tagId).persons;
      @ ensures getPerson(personId2).getTag(tagId).hasPerson(getPerson(personId1));
      @ also
      @ public normal_behavior
      @ requires containsPerson(personId1) &&
      @          containsPerson(personId2) &&
      @          personId1!=personId2      &&
      @          getPerson(personId2).isLinked(getPerson(personId1)) &&
      @          getPerson(personId2).containsTag(tagId) &&
      @          !getPerson(personId2).getTag(tagId).hasPerson(getPerson(personId1)) &&
      @          getPerson(personId2).getTag(tagId).persons.length > 1111;
      @ assignable \nothing
      @ also
      @ public exceptional_behavior
      @ signals (PersonIdNotFoundException e) !containsPerson(personId1);
      @ signals (PersonIdNotFoundException e) containsPerson(personId1) &&
      @                                       !containsPerson(personId2);
      @ signals (EqualPersonIdException e)    containsPerson(personId1) &&
      @                                       containsPerson(personId2) &&
      @                                       personId1==personId2 ;
      @ signals (RelationNotFoundException e) containsPerson(personId1) &&
      @                                       containsPerson(personId2) &&
      @                                       personId1!=personId2      &&
      @                                       !getPerson(personId2).isLinked(getPerson(personId1));
      @ signals (TagIdNotFoundException e) containsPerson(personId1) &&
      @                                    containsPerson(personId2) &&
      @                                    personId1!=personId2      &&
      @                                    getPerson(personId2).isLinked(getPerson(personId1)) &&
      @                                    !getPerson(personId2).containsTag(tagId);
      @ signals (EqualPersonIdException e) containsPerson(personId1) &&
      @                                    containsPerson(personId2) &&
      @                                    personId1!=personId2      &&
      @                                    getPerson(personId2).isLinked(getPerson(personId1)) &&
      @                                    getPerson(personId2).containsTag(tagId) &&
      @                                    getPerson(personId2).getTag(tagId).hasPerson(getPerson(personId1));
      @*/
    public /*@ safe @*/ void addPersonToTag(int personId1,int personId2, int tagId) throws PersonIdNotFoundException,
            RelationNotFoundException, TagIdNotFoundException, EqualPersonIdException;

    /*@ public normal_behavior
      @ requires containsPerson(personId) &&
      @          getPerson(personId).containsTag(tagId);
      @ ensures \result == getPerson(personId).getTag(tagId).getValueSum();
      @ also
      @ public exceptional_behavior
      @ signals (PersonIdNotFoundException e) !containsPerson(personId);
      @ signals (TagIdNotFoundException e) containsPerson(personId) &&
      @                                    !getPerson(personId).containsTag(tagId);
      @*/
    public /*@ pure @*/ int queryTagValueSum(int personId,int tagId) throws PersonIdNotFoundException,TagIdNotFoundException;

    /*@ public normal_behavior
      @ requires containsPerson(personId) &&
      @          getPerson(personId).containsTag(tagId);
      @ ensures \result == getPerson(personId).getTag(tagId).getAgeVar();
      @ also
      @ public exceptional_behavior
      @ signals (PersonIdNotFoundException e) !containsPerson(personId);
      @ signals (TagIdNotFoundException e) containsPerson(personId) &&
      @                                    !getPerson(personId).containsTag(tagId);
      @*/
    public /*@ pure @*/ int queryTagAgeVar(int personId,int tagId) throws PersonIdNotFoundException,TagIdNotFoundException;

    /*@ public normal_behavior
      @ requires containsPerson(personId1) &&
      @          containsPerson(personId2) &&
      @          getPerson(personId2).containsTag(tagId) &&
      @          getPerson(personId2).getTag(tagId).hasPerson(getPerson(personId1));
      @ assignable getPerson(personId2).getTag(tagId).persons;
      @ ensures !getPerson(personId2).getTag(tagId).hasPerson(getPerson(personId1));
      @ also
      @ public exceptional_behavior
      @ signals (PersonIdNotFoundException e) !containsPerson(personId1);
      @ signals (PersonIdNotFoundException e) containsPerson(personId1) &&
      @                                        !containsPerson(personId2);
      @ signals (TagIdNotFoundException e) containsPerson(personId1) &&
      @                                    containsPerson(personId2) &&
      @                                    !getPerson(personId2).containsTag(tagId);
      @ signals (PersonIdNotFoundException e) containsPerson(personId1) &&
      @                                     containsPerson(personId2) &&
      @                                     getPerson(personId2).containsTag(tagId);
      @                                     !getPerson(personId2).getTag(tagId).hasPerson(getPerson(personId1));
      @*/
    public /*@ safe @*/ void delPersonFromTag(int personId1, int personId2,int tagId) throws  PersonIdNotFoundException,
            TagIdNotFoundException;



    /*@ public normal_behavior
      @ requires containsPerson(personId) &&
      @          getPerson(personId).containsTag(tagId);
      @ assignable getPerson(personId).tags;
      @ ensures !getPerson(personId).containsTag(tagId);
      @ also
      @ public exceptional_behavior
      @ signals (PersonIdNotFoundException e) !containsPerson(personId);
      @ signals (TagIdNotFoundException e) containsPerson(personId) &&
      @                                    !getPerson(personId).containsTag(tagId);
     */
    public /*@ safe @*/ void delTag(int personId,int tagId) throws  PersonIdNotFoundException,
            TagIdNotFoundException;

    /*@ public normal_behavior
      @ requires containsPerson(id) && getPerson(id).acquaintance.length != 0;
      @ ensures \result == (\min int bestId;
      @         (\exists int i; 0 <= i && i < getPerson(id).acquaintance.length &&
      @             getPerson(id).acquaintance[i].getId() == bestId;
      @             (\forall int j; 0 <= j && j < getPerson(id).acquaintance.length;
      @                 getPerson(id).value[j] <= getPerson(id).value[i]));
      @         bestId);
      @ public exceptional_behavior
      @ signals (PersonIdNotFoundException e) !containsPerson(id);
      @ signals (AcquaintanceNotFoundException e) containsPerson(id) &&
      @         getPerson(id).acquaintance.length == 0;
      @*/
    public /*@ pure @*/ int queryBestAcquaintance(int id) throws
            PersonIdNotFoundException, AcquaintanceNotFoundException;


    /*@ ensures \result ==
      @         (\sum int i, j; 0 <= i && i < j && j < persons.length
      @                         && persons[i].acquaintance.length > 0 && queryBestAcquaintance(persons[i].getId()) == persons[j].getId()
      @                         && persons[j].acquaintance.length > 0 && queryBestAcquaintance(persons[j].getId()) == persons[i].getId();
      @                         1);
      @*/
    public /*@ pure @*/ int queryCoupleSum();


    /*@ public normal_behavior
      @ requires containsPerson(id1) &&
      @          containsPerson(id2) &&
      @          (\exists Person[] path;
      @          path.length >= 2 &&
      @          path[0].equals(getPerson(id1)) &&
      @          path[path.length - 1].equals(getPerson(id2));
      @          (\forall int i; 1 <= i && i < path.length; path[i - 1].isLinked(path[i])));
      @ ensures  (\exists Person[] pathM;
      @          pathM.length >= 2 &&
      @          pathM[0].equals(getPerson(id1)) &&
      @          pathM[pathM.length - 1].equals(getPerson(id2)) &&
      @          (\forall int i; 1 <= i && i < pathM.length; pathM[i - 1].isLinked(pathM[i]));
      @          (\forall Person[] path;
      @          path.length >= 2 &&
      @          path[0].equals(getPerson(id1)) &&
      @          path[path.length - 1].equals(getPerson(id2)) &&
      @          (\forall int i; 1 <= i && i < path.length; path[i - 1].isLinked(path[i]));
      @          (\sum int i; 0 <= i && i < path.length; 1) >=
      @          (\sum int i; 0 <= i && i < pathM.length; 1)) &&
      @          \result==(\sum int i; 1 <= i && i < pathM.length - 1; 1));
      @ also
      @ public exceptional_behavior
      @ signals (PersonIdNotFoundException e) !containsPerson(id1);
      @ signals (PersonIdNotFoundException e) containsPerson(id1) &&
      @                                       !containsPerson(id2);
      @ signals (PathNotFoundException e) containsPerson(id1) &&
      @                                   containsPerson(id2) &&
      @         !(\exists Person[] path;
      @         path.length >= 2 &&
      @         path[0].equals(getPerson(id1)) &&
      @         path[path.length - 1].equals(getPerson(id2));
      @         (\forall int i; 1 <= i && i < path.length; path[i - 1].isLinked(path[i])));
      @*/
    public /*@ pure @*/ int queryShortestPath(int id1,int id2) throws PersonIdNotFoundException, PathNotFoundException;
}
