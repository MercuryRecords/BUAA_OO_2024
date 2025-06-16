package com.oocourse.spec3.main;

import java.util.List;

import com.oocourse.spec3.exceptions.*;

public interface Network {
    

    /*@ public instance model non_null Person[] persons;
      @ public instance model non_null Message[] messages;
      @ public instance model non_null int[] emojiIdList;
      @ public instance model non_null int[] emojiHeatList;
      @*/

    /*@ invariant persons != null && (\forall int i,j; 0 <= i && i < j && j < persons.length; !persons[i].equals(persons[j])) &&
      @           messages != null && (\forall int i,j; 0 <= i && i < j && j < messages.length; !messages[i].equals(messages[j])) &&
      @           emojiIdList != null && (\forall int i,j; 0 <= i && i < j && j < emojiIdList.length; emojiIdList[i] != emojiIdList[j]) &&
      @           emojiIdList.length == emojiHeatList.length;
      @ */

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
      @                      \old(getPerson(id1).tags[i].hasPerson(getPerson(id2)))==>!getPerson(id1).tags[i].hasPerson(getPerson(id2)));
      @ ensures  (\forall int i; 0 <= i && i < getPerson(id2).tags.length;
      @                      \old(getPerson(id2).tags[i].hasPerson(getPerson(id1)))==>!getPerson(id2).tags[i].hasPerson(getPerson(id1)));
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

    //@ ensures \result == (\exists int i; 0 <= i && i < messages.length; messages[i].getId() == id);
    public /*@ pure @*/ boolean containsMessage(int id);

    /*@ public normal_behavior
      @ requires !containsMessage(message.getId()) &&
      @           (message instanceof EmojiMessage) ==> containsEmojiId(((EmojiMessage) message).getEmojiId()) &&
      @            (message.getType() == 0) ==> !message.getPerson1().equals(message.getPerson2());
      @ assignable messages;
      @ ensures containsMessage(message.getId());
      @ also
      @ public exceptional_behavior
      @ signals (EqualMessageIdException e) containsMessage(message.getId());
      @ signals (EmojiIdNotFoundException e) !containsMessage(message.getId()) &&
      @                                       (message instanceof EmojiMessage) &&
      @                                       !containsEmojiId(((EmojiMessage) message).getEmojiId());
      @ signals (EqualPersonIdException e) !containsMessage(message.getId()) &&
      @                                     (message instanceof EmojiMessage) ==>
      @                                     containsEmojiId(((EmojiMessage) message).getEmojiId())) &&
      @                                     message.getType() == 0 &&
      @                                     message.getPerson1().equals(message.getPerson2());
      @*/
    public /*@ safe @*/ void addMessage(Message message) throws
            EqualMessageIdException, EmojiIdNotFoundException, EqualPersonIdException;

    /*@ public normal_behavior
      @ requires containsMessage(id);
      @ ensures (\exists int i; 0 <= i && i < messages.length; messages[i].getId() == id &&
      @         \result == messages[i]);
      @ public normal_behavior
      @ requires !containsMessage(id);
      @ ensures \result == null;
      @*/
    public /*@ pure @*/ Message getMessage(int id);

    /*@ public normal_behavior
      @ requires containsMessage(id) && getMessage(id).getType() == 0 &&
      @          getMessage(id).getPerson1().isLinked(getMessage(id).getPerson2()) &&
      @          getMessage(id).getPerson1() != getMessage(id).getPerson2();
      @ assignable persons[*], messages, emojiHeatList[*];
      @ assignable getMessage(id).getPerson1().socialValue, getMessage(id).getPerson1().money;
      @ assignable getMessage(id).getPerson2().messages, getMessage(id).getPerson2().socialValue, getMessage(id).getPerson2().money;
      @ ensures !containsMessage(id);
      @ ensures \old(getMessage(id)).getPerson1().getSocialValue() ==
      @         \old(getMessage(id).getPerson1().getSocialValue()) + \old(getMessage(id)).getSocialValue() &&
      @         \old(getMessage(id)).getPerson2().getSocialValue() ==
      @         \old(getMessage(id).getPerson2().getSocialValue()) + \old(getMessage(id)).getSocialValue();
      @ ensures (\old(getMessage(id)) instanceof RedEnvelopeMessage) ==>
      @         (\old(getMessage(id)).getPerson1().getMoney() ==
      @         \old(getMessage(id).getPerson1().getMoney()) - ((RedEnvelopeMessage)\old(getMessage(id))).getMoney() &&
      @         \old(getMessage(id)).getPerson2().getMoney() ==
      @         \old(getMessage(id).getPerson2().getMoney()) + ((RedEnvelopeMessage)\old(getMessage(id))).getMoney());
      @ ensures (!(\old(getMessage(id)) instanceof RedEnvelopeMessage)) ==> (\not_assigned(persons[*].money));
      @ ensures (\old(getMessage(id)) instanceof EmojiMessage) ==>
      @         (\exists int i; 0 <= i && i < emojiIdList.length && emojiIdList[i] == ((EmojiMessage)\old(getMessage(id))).getEmojiId();
      @         emojiHeatList[i] == \old(emojiHeatList[i]) + 1);
      @ ensures (!(\old(getMessage(id)) instanceof EmojiMessage)) ==> \not_assigned(emojiHeatList);
      @ ensures (\forall int i; 0 <= i && i < \old(getMessage(id).getPerson2().getMessages().size());
      @          \old(getMessage(id)).getPerson2().getMessages().get(i+1) == \old(getMessage(id).getPerson2().getMessages().get(i)));
      @ ensures \old(getMessage(id)).getPerson2().getMessages().get(0).equals(\old(getMessage(id)));
      @ ensures \old(getMessage(id)).getPerson2().getMessages().size() == \old(getMessage(id).getPerson2().getMessages().size()) + 1;
      @ also
      @ public normal_behavior
      @ requires containsMessage(id) && getMessage(id).getType() == 1 && 
      @           getMessage(id).getPerson1().containsTag(getMessage(id).getTag().getId());
      @ assignable persons[*], messages, emojiHeatList[*];
      @ ensures !containsMessage(id)
      @ ensures \old(getMessage(id)).getPerson1().getSocialValue() ==
      @         \old(getMessage(id).getPerson1().getSocialValue())+ \old(getMessage(id)).getsocialValue();
      @ ensures (\forall Person p; \old(getMessage(id)).getTag().hasPerson(p); p.getSocialValue() ==
      @         \old(p.getSocialValue()) + \old(getMessage(id)).getSocialValue());
      @ ensures (\old(getMessage(id)) instanceof RedEnvelopeMessage) && (\old(getMessage(id)).getTag().getSize() > 0) ==>
      @          (\exists int i; i == ((RedEnvelopeMessage)\old(getMessage(id))).getMoney()/\old(getMessage(id)).getTag().getSize();
      @           \old(getMessage(id)).getPerson1().getMoney() ==
      @           \old(getMessage(id).getPerson1().getMoney()) - i*\old(getMessage(id)).getTag().getSize() &&
      @           (\forall Person p; \old(getMessage(id)).getTag().hasPerson(p);
      @           p.getMoney() == \old(p.getMoney()) + i));

      @ ensures (\old(getMessage(id)) instanceof EmojiMessage) ==>
      @         (\exists int i; 0 <= i && i < emojiIdList.length && emojiIdList[i] == ((EmojiMessage)\old(getMessage(id))).getEmojiId();
      @          emojiHeatList[i] == \old(emojiHeatList[i]) + 1);
      @ also
      @ public exceptional_behavior
      @ signals (MessageIdNotFoundException e) !containsMessage(id);
      @ signals (RelationNotFoundException e) containsMessage(id) && getMessage(id).getType() == 0 &&
      @          !(getMessage(id).getPerson1().isLinked(getMessage(id).getPerson2()));
      @ signals (TagIdNotFoundException e) containsMessage(id) && getMessage(id).getType() == 1 &&
      @          !getMessage(id).getPerson1().containsTag(getMessage(id).getTag().getId());
      @*/
    public /*@ safe @*/ void sendMessage(int id) throws
            RelationNotFoundException, MessageIdNotFoundException, TagIdNotFoundException;

    /*@ public normal_behavior
      @ requires containsPerson(id);
      @ ensures \result == getPerson(id).getSocialValue();
      @ also
      @ public exceptional_behavior
      @ signals (PersonIdNotFoundException e) !containsPerson(id);
      @*/
    public /*@ pure @*/ int querySocialValue(int id) throws PersonIdNotFoundException;

    /*@ public normal_behavior
      @ requires containsPerson(id);
      @ ensures \result == getPerson(id).getReceivedMessages();
      @ also
      @ public exceptional_behavior
      @ signals (PersonIdNotFoundException e) !containsPerson(id);
      @*/
    public /*@ pure @*/ List<Message> queryReceivedMessages(int id) throws PersonIdNotFoundException;

    //@ ensures \result == (\exists int i; 0 <= i && i < emojiIdList.length; emojiIdList[i] == id);
    public /*@ pure @*/ boolean containsEmojiId(int id);

    /*@ public normal_behavior
      @ requires !containsEmojiId(id);
      @ assignable emojiIdList, emojiHeatList;
      @ ensures (\exists int i; 0 <= i && i < emojiIdList.length; emojiIdList[i] == id && emojiHeatList[i] == 0);
      @ ensures emojiIdList.length == \old(emojiIdList.length) + 1 &&
      @          emojiHeatList.length == \old(emojiHeatList.length) + 1;
      @ ensures (\forall int i; 0 <= i && i < \old(emojiIdList.length); 
      @          (\exists int j; 0 <= j && j < emojiIdList.length; emojiIdList[j] == \old(emojiIdList[i]) &&
      @          emojiHeatList[j] == \old(emojiHeatList[i])));
      @ also
      @ public exceptional_behavior
      @ signals (EqualEmojiIdException e) containsEmojiId(id);
      @*/
    public void storeEmojiId(int id) throws EqualEmojiIdException;

    /*@ public normal_behavior
      @ requires containsPerson(id);
      @ ensures \result == getPerson(id).getMoney();
      @ also
      @ public exceptional_behavior
      @ signals (PersonIdNotFoundException e) !containsPerson(id);
      @*/
    public /*@ pure @*/ int queryMoney(int id) throws PersonIdNotFoundException;

    /*@ public normal_behavior
      @ requires containsEmojiId(id);
      @ ensures (\exists int i; 0 <= i && i < emojiIdList.length; emojiIdList[i] == id &&
      @          \result == emojiHeatList[i]);
      @ also
      @ public exceptional_behavior
      @ requires !containsEmojiId(id);
      @ signals_only EmojiIdNotFoundException;
      @*/
    public /*@ pure @*/ int queryPopularity(int id) throws EmojiIdNotFoundException;

    /*@ public normal_behavior
      @ assignable emojiIdList, emojiHeatList, messages;
      @ ensures (\forall int i; 0 <= i && i < \old(emojiIdList.length);
      @          (\old(emojiHeatList[i] >= limit) ==>
      @          (\exists int j; 0 <= j && j < emojiIdList.length; emojiIdList[j] == \old(emojiIdList[i]))));
      @ ensures (\forall int i; 0 <= i && i < emojiIdList.length;
      @          (\exists int j; 0 <= j && j < \old(emojiIdList.length);
      @          emojiIdList[i] == \old(emojiIdList[j]) && emojiHeatList[i] == \old(emojiHeatList[j])));
      @ ensures emojiIdList.length ==
      @          (\num_of int i; 0 <= i && i < \old(emojiIdList.length); \old(emojiHeatList[i] >= limit));
      @ ensures emojiIdList.length == emojiHeatList.length;
      @ ensures (\forall int i; 0 <= i && i < \old(messages.length);
      @          (\old(messages[i]) instanceof EmojiMessage &&
      @           containsEmojiId(\old(((EmojiMessage)messages[i]).getEmojiId()))  ==> \not_assigned(\old(messages[i])) &&
      @           (\exists int j; 0 <= j && j < messages.length; messages[j].equals(\old(messages[i])))));
      @ ensures (\forall int i; 0 <= i && i < \old(messages.length);
      @          (!(\old(messages[i]) instanceof EmojiMessage) ==> \not_assigned(\old(messages[i])) &&
      @           (\exists int j; 0 <= j && j < messages.length; messages[j].equals(\old(messages[i])))));
      @ ensures messages.length == (\num_of int i; 0 <= i && i <= \old(messages.length);
      @          (\old(messages[i]) instanceof EmojiMessage) ==>
      @           (containsEmojiId(\old(((EmojiMessage)messages[i]).getEmojiId()))));
      @ ensures \result == emojiIdList.length;
      @*/
    public int deleteColdEmoji(int limit);

    /*@ public normal_behavior
      @ requires containsPerson(personId);
      @ assignable getPerson(personId).messages;
      @ ensures (\forall Message i; \old(getPerson(personId).getMessages().contains(i));
      @           !(i instanceof NoticeMessage) ==>
      @             (\exists Message j; getPerson(personId).getMessages().contains(j); i.equals(j)));
      @ ensures getPerson(personId).messages.length ==
      @           (\num_of int i; 0 <= i && i < \old(getPerson(personId).messages.length);
      @             !(\old(getPerson(personId).getMessages().get(i)) instanceof NoticeMessage));
      @ ensures (\forall int i; 0 <= i && i < getPerson(personId).getMessages().size();
      @           (\forall int j; i < j && j < getPerson(personId).getMessages().size();
      @                 \old(getPerson(personId).getMessages()).indexOf(
      @                   getPerson(personId).getMessages().get(i)) <
      @                 \old(getPerson(personId).getMessages()).indexOf(
      @                   getPerson(personId).getMessages().get(j))));
      @ also
      @ public exceptional_behavior
      @ signals (PersonIdNotFoundException e) !containsPerson(personId);
      @*/
    public void clearNotices(int personId) throws PersonIdNotFoundException;

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
