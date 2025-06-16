package com.oocourse.spec3.main;

import java.io.FileReader;
import java.io.PrintStream;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.util.List;
import java.util.Scanner;

import com.oocourse.spec3.exceptions.*;

public class Runner {

    private String[] commands;
    private Network network;
    private final Constructor<? extends Person> personConstructor;
    private final Constructor<? extends Network> networkConstructor;
    private final Constructor<? extends Tag> tagConstructor;
    private final Constructor<? extends Message> messageConstructor0;
    private final Constructor<? extends Message> messageConstructor1;
    private final Constructor<? extends EmojiMessage> emojiConstructor0;
    private final Constructor<? extends EmojiMessage> emojiConstructor1;
    private final Constructor<? extends RedEnvelopeMessage> redEnvelopeConstructor0;
    private final Constructor<? extends RedEnvelopeMessage> redEnvelopeConstructor1;
    private final Constructor<? extends NoticeMessage> noticeConstructor0;
    private final Constructor<? extends NoticeMessage> noticeConstructor1;
    private final Scanner scanner;

    public Runner(Class<? extends Person> personClass, Class<? extends Network> networkClass,
            Class<? extends Tag> tagClass, Class<? extends Message> messageClass,
            Class<? extends EmojiMessage> emojiClass,
            Class<? extends NoticeMessage> noticeClass,
            Class<? extends RedEnvelopeMessage> redEnvelopeClass) {
        try {
            personConstructor = personClass.getConstructor(
                    int.class, String.class, int.class);
            networkConstructor = networkClass.getConstructor();
            tagConstructor = tagClass.getConstructor(int.class);
            messageConstructor0 = messageClass.getConstructor(int.class, int.class, Person.class, Person.class);
            messageConstructor1 = messageClass.getConstructor(int.class, int.class, Person.class, Tag.class);
            emojiConstructor0 = emojiClass.getConstructor(int.class, int.class, Person.class, Person.class);
            emojiConstructor1 = emojiClass.getConstructor(int.class, int.class, Person.class, Tag.class);
            noticeConstructor0 = noticeClass.getConstructor(int.class, String.class, Person.class, Person.class);
            noticeConstructor1 = noticeClass.getConstructor(int.class, String.class, Person.class, Tag.class);
            redEnvelopeConstructor0 = redEnvelopeClass.getConstructor(int.class, int.class, Person.class, Person.class);
            redEnvelopeConstructor1 = redEnvelopeClass.getConstructor(int.class, int.class, Person.class, Tag.class);

            scanner = new Scanner(System.in);
        } catch (NoSuchMethodException e) {
            throw new RuntimeException(e);
        }
    }

    public Runner(Class<? extends Person> personClass, Class<? extends Network> networkClass,
            Class<? extends Tag> tagClass, Class<? extends Message> messageClass,
            Class<? extends EmojiMessage> emojiClass,
            Class<? extends NoticeMessage> noticeClass,
            Class<? extends RedEnvelopeMessage> redEnvelopeClass,
            PrintStream printStream) {
        this(personClass, networkClass, tagClass, messageClass, emojiClass, noticeClass, redEnvelopeClass);
        System.setOut(printStream);
    }

    public void run() {
        try {

            this.network = this.networkConstructor.newInstance();
            while (scanner.hasNextLine()) {
                String cmd = scanner.nextLine();
                commands = cmd.split(" ");
                switch (commands[0]) {
                    case "ap":
                    case "add_person":
                        addPerson();
                        break;
                    case "ar":
                    case "add_relation":
                        addRelation();
                        break;
                    case "qv":
                    case "query_value":
                        queryValue();
                        break;
                    case "qci":
                    case "query_circle":
                        queryCircle();
                        break;
                    case "qbs":
                    case "query_block_sum":
                        queryBlockSum();
                        break;
                    case "qts":
                    case "query_triple_sum":
                        queryTripleSum();
                        break;
                    case "at":
                    case "add_tag":
                        addTag();
                        break;
                    case "att":
                    case "add_to_tag":
                        addToTag();
                        break;
                    case "dft":
                    case "del_from_tag":
                        delFromTag();
                        break;
                    case "qtvs":
                    case "query_tag_value_sum":
                        queryTagValueSum();
                        break;
                    case "qtav":
                    case "query_tag_age_var":
                        queryTagAgeVar();
                        break;
                    case "mr":
                    case "modify_relation":
                        modifyRelation();
                        break;
                    case "qba":
                    case "query_best_acquaintance":
                        queryBestAcquaintance();
                        break;
                    case "qcs":
                    case "query_couple_sum":
                        queryCoupleSum();
                        break;
                    case "qsp":
                    case "query_shortest_path":
                        queryShortestPath();
                        break;
                    case "dt":
                    case "del_tag":
                        delTag();
                        break;
                    case "am":
                    case "add_message":
                        addMessage();
                        break;
                    case "sm":
                    case "send_message":
                        sendMessage();
                        break;
                    case "qsv":
                    case "query_social_value":
                        querySocialValue();
                        break;
                    case "qrm":
                    case "query_received_messages":
                        queryReceivedMessages();
                        break;
                    case "arem":
                    case "add_red_envelope_message":
                        addRedEnvelopeMessage();
                        break;
                    case "anm":
                    case "add_notice_message":
                        addNoticeMessage();
                        break;
                    case "cn":
                    case "clear_notices":
                        clearNotices();
                        break;
                    case "aem":
                    case "add_emoji_message":
                        addEmojiMessage();
                        break;
                    case "sei":
                    case "store_emoji_id":
                        storeEmojiId();
                        break;
                    case "qp":
                    case "query_popularity":
                        queryPopularity();
                        break;
                    case "dce":
                    case "delete_cold_emoji":
                        deleteColdEmoji();
                        break;
                    case "qm":
                    case "query_money":
                        queryMoney();
                        break;
                    case "ln":
                    case "load_network":
                        loadNetwork(scanner);
                        break;
                    case "lnl":
                    case "load_network_local":
                        try {
                            loadNetwork(new Scanner(new FileReader(commands[2])));
                        } catch (Exception e) {
                            System.out.println("File not found");
                            return;
                        }
                        break;
                    default:
                        throw new RuntimeException("No such command");
                }
            }
            scanner.close();
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    private void clearNotices() {
        int id = Integer.parseInt(commands[1]);
        try {
            network.clearNotices(id);
        } catch (PersonIdNotFoundException e) {
            e.print();
            return;
        }
        System.out.println("Ok");
    }

    private void queryMoney() {
        int id = Integer.parseInt(commands[1]);
        int ret;
        try {
            ret = network.queryMoney(id);
        } catch (PersonIdNotFoundException e) {
            e.print();
            return;
        }
        System.out.println(ret);
    }

    private void storeEmojiId() {
        int id = Integer.parseInt(commands[1]);
        try {
            network.storeEmojiId(id);
        } catch (EqualEmojiIdException e) {
            e.print();
            return;
        }
        System.out.println("Ok");
    }

    private boolean addMessage(Message message) {
        try {
            network.addMessage(message);
        } catch (EqualMessageIdException e) {
            e.print();
            return true;
        } catch (EmojiIdNotFoundException e) {
            e.print();
            return true;
        } catch (EqualPersonIdException e) {
            e.print();
            return true;
        }
        return false;
    }

    private void addMessage() throws IllegalAccessException, InvocationTargetException,
            InstantiationException {
        int id = Integer.parseInt(commands[1]);
        int socialValue = Integer.parseInt(commands[2]);
        int type = Integer.parseInt(commands[3]);
        int id1 = Integer.parseInt(commands[4]);
        int id2 = Integer.parseInt(commands[5]);
        if (type == 0) {
            if (!network.containsPerson(id1) || !network.containsPerson(id2)) {
                System.out.println("The person with this number does not exist");
                return;
            }
            Person person1 = network.getPerson(id1);
            Person person2 = network.getPerson(id2);
            Message message = this.messageConstructor0.newInstance(id, socialValue, person1,
                    person2);
            if (addMessage(message)) {
                return;
            }
        } else if (type == 1) {
            if (!network.containsPerson(id1)) {
                System.out.println("The person with this number does not exist");
                return;
            }
            Person person1 = network.getPerson(id1);
            Tag tag = person1.getTag(id2);
            if (tag == null) {
                System.out.println("Tag does not exist");
                return;
            }
            Message message = this.messageConstructor1.newInstance(id, socialValue, person1, tag);
            if (addMessage(message)) {
                return;
            }
        } else {
            return;
        }
        System.out.println("Ok");
    }

    private void addRedEnvelopeMessage()
            throws IllegalAccessException, InvocationTargetException, InstantiationException {
        int id = Integer.parseInt(commands[1]);
        int money = Integer.parseInt(commands[2]);
        int type = Integer.parseInt(commands[3]);
        int id1 = Integer.parseInt(commands[4]);
        int id2 = Integer.parseInt(commands[5]);
        if (type == 0) {
            if (!network.containsPerson(id1) || !network.containsPerson(id2)) {
                System.out.println("The person with this number does not exist");
                return;
            }
            Person person1 = network.getPerson(id1);
            Person person2 = network.getPerson(id2);
            RedEnvelopeMessage message = this.redEnvelopeConstructor0.newInstance(id, money,
                    person1, person2);
            if (addMessage(message)) {
                return;
            }
        } else if (type == 1) {
            if (!network.containsPerson(id1)) {
                System.out.println("The person with this number does not exist");
                return;
            }
            Person person1 = network.getPerson(id1);
            Tag tag = person1.getTag(id2);
            if (tag == null) {
                System.out.println("Tag does not exist");
                return;
            }
            RedEnvelopeMessage message = this.redEnvelopeConstructor1.newInstance(id, money,
                    person1, tag);
            if (addMessage(message)) {
                return;
            }
        } else {
            return;
        }
        System.out.println("Ok");
    }

    private void addNoticeMessage() throws IllegalAccessException, InvocationTargetException,
            InstantiationException {
        int id = Integer.parseInt(commands[1]);
        String string = commands[2];
        int type = Integer.parseInt(commands[3]);
        int id1 = Integer.parseInt(commands[4]);
        int id2 = Integer.parseInt(commands[5]);
        if (type == 0) {
            if (!network.containsPerson(id1) || !network.containsPerson(id2)) {
                System.out.println("The person with this number does not exist");
                return;
            }
            Person person1 = network.getPerson(id1);
            Person person2 = network.getPerson(id2);
            NoticeMessage message = this.noticeConstructor0.newInstance(id, string, person1,
                    person2);
            if (addMessage(message)) {
                return;
            }
        } else if (type == 1) {
            if (!network.containsPerson(id1)) {
                System.out.println("The person with this number does not exist");
                return;
            }
            Person person1 = network.getPerson(id1);
            Tag tag = person1.getTag(id2);
            if (tag == null) {
                System.out.println("Tag does not exist");
                return;
            }
            NoticeMessage message = this.noticeConstructor1.newInstance(id, string, person1, tag);
            if (addMessage(message)) {
                return;
            }
        } else {
            return;
        }
        System.out.println("Ok");
    }

    private void addEmojiMessage() throws IllegalAccessException, InvocationTargetException,
            InstantiationException {
        int id = Integer.parseInt(commands[1]);
        int emojiId = Integer.parseInt(commands[2]);
        int type = Integer.parseInt(commands[3]);
        int id1 = Integer.parseInt(commands[4]);
        int id2 = Integer.parseInt(commands[5]);
        if (type == 0) {
            if (!network.containsPerson(id1) || !network.containsPerson(id2)) {
                System.out.println("The person with this number does not exist");
                return;
            }
            Person person1 = network.getPerson(id1);
            Person person2 = network.getPerson(id2);
            EmojiMessage message = this.emojiConstructor0.newInstance(id, emojiId, person1,
                    person2);
            if (addMessage(message)) {
                return;
            }
        } else if (type == 1) {
            if (!network.containsPerson(id1)) {
                System.out.println("The person with this number does not exist");
                return;
            }
            Person person1 = network.getPerson(id1);
            Tag tag = person1.getTag(id2);
            if (tag == null) {
                System.out.println("Tag does not exist");
                return;
            }
            EmojiMessage message = this.emojiConstructor1.newInstance(id, emojiId, person1, tag);
            if (addMessage(message)) {
                return;
            }
        } else {
            return;
        }
        System.out.println("Ok");
    }

    private void queryPopularity() {
        int id = Integer.parseInt(commands[1]);
        int ret;
        try {
            ret = network.queryPopularity(id);
        } catch (EmojiIdNotFoundException e) {
            e.print();
            return;
        }
        System.out.println(ret);
    }

    private void deleteColdEmoji() {
        int limit = Integer.parseInt(commands[1]);
        System.out.println(network.deleteColdEmoji(limit));
    }

    private void queryReceivedMessages() {
        int id = Integer.parseInt(commands[1]);
        List<Message> list;
        try {
            list = network.queryReceivedMessages(id);
        } catch (PersonIdNotFoundException e) {
            e.print();
            return;
        }
        if (list.isEmpty()) {
            System.out.println("None");
        } else {
            int i = 0;
            for (; i < list.size() - 1; i++) {
                Message message = list.get(i);
                resolve(message);
                System.out.print("; ");
            }
            Message message = list.get(i);
            resolve(message);
            System.out.println();
        }
    }

    private void sendMessage() {
        int messageId = Integer.parseInt(commands[1]);
        try {
            network.sendMessage(messageId);
        } catch (RelationNotFoundException e) {
            e.print();
            return;
        } catch (MessageIdNotFoundException e) {
            e.print();
            return;
        } catch (TagIdNotFoundException e) {
            e.print();
            return;
        }
        System.out.println("Ok");
    }

    private void delTag() {
        int id = Integer.parseInt(commands[1]);
        int tagId = Integer.parseInt(commands[2]);
        try {
            network.delTag(id, tagId);
        } catch (PersonIdNotFoundException e) {
            e.print();
            return;
        } catch (TagIdNotFoundException e) {
            e.print();
            return;
        }
        System.out.println("Ok");
    }

    private void queryCoupleSum() {
        System.out.println(network.queryCoupleSum());
    }

    private void queryTripleSum() {
        System.out.println(network.queryTripleSum());
    }

    private void queryShortestPath() {
        int id1 = Integer.parseInt(commands[1]);
        int id2 = Integer.parseInt(commands[2]);
        int ret;
        try {
            ret = network.queryShortestPath(id1, id2);
        } catch (PersonIdNotFoundException e) {
            e.print();
            return;
        } catch (PathNotFoundException e) {
            e.print();
            return;
        }
        System.out.println(ret);
    }

    private void queryBlockSum() {
        System.out.println(network.queryBlockSum());
    }

    private void delFromTag() {
        int id1 = Integer.parseInt(commands[1]);
        int id2 = Integer.parseInt(commands[2]);
        int tagId = Integer.parseInt(commands[3]);
        try {
            network.delPersonFromTag(id1, id2, tagId);
        } catch (PersonIdNotFoundException e) {
            e.print();
            return;
        } catch (TagIdNotFoundException e) {
            e.print();
            return;
        }
        System.out.println("Ok");
    }

    private void queryTagAgeVar() {
        int id = Integer.parseInt(commands[1]);
        int tagId = Integer.parseInt(commands[2]);
        int ret;
        try {
            ret = network.queryTagAgeVar(id, tagId);
        } catch (TagIdNotFoundException e) {
            e.print();
            return;
        } catch (PersonIdNotFoundException e) {
            e.print();
            return;
        }
        System.out.println(ret);
    }

    private void queryTagValueSum() {
        int id = Integer.parseInt(commands[1]);
        int tagId = Integer.parseInt(commands[2]);
        int ret;
        try {
            ret = network.queryTagValueSum(id, tagId);
        } catch (TagIdNotFoundException e) {
            e.print();
            return;
        } catch (PersonIdNotFoundException e) {
            e.print();
            return;
        }
        System.out.println(ret);
    }

    private void addToTag() {
        int id1 = Integer.parseInt(commands[1]);
        int id2 = Integer.parseInt(commands[2]);
        int tagId = Integer.parseInt(commands[3]);
        try {
            network.addPersonToTag(id1, id2, tagId);
        } catch (TagIdNotFoundException e) {
            e.print();
            return;
        } catch (PersonIdNotFoundException e) {
            e.print();
            return;
        } catch (EqualPersonIdException e) {
            e.print();
            return;
        } catch (RelationNotFoundException e) {
            e.print();
            return;
        }
        System.out.println("Ok");
    }

    private void addTag()
            throws InstantiationException, IllegalAccessException,
            IllegalArgumentException, InvocationTargetException {
        int id = Integer.parseInt(commands[1]);
        int tagId = Integer.parseInt(commands[2]);
        try {
            network.addTag(id, this.tagConstructor.newInstance(tagId));
        } catch (EqualTagIdException e) {
            e.print();
            return;
        } catch (PersonIdNotFoundException e) {
            e.print();
            return;
        }
        System.out.println("Ok");
    }

    private void queryCircle() {
        int id1 = Integer.parseInt(commands[1]);
        int id2 = Integer.parseInt(commands[2]);
        try {
            System.out.println(network.isCircle(id1, id2));
        } catch (PersonIdNotFoundException e) {
            e.print();
        }
    }

    private void queryValue() {
        int id1 = Integer.parseInt(commands[1]);
        int id2 = Integer.parseInt(commands[2]);
        int ret;
        try {
            ret = network.queryValue(id1, id2);
        } catch (PersonIdNotFoundException e) {
            e.print();
            return;
        } catch (RelationNotFoundException e) {
            e.print();
            return;
        }
        System.out.println(ret);
    }

    private void addRelation() {
        int id1 = Integer.parseInt(commands[1]);
        int id2 = Integer.parseInt(commands[2]);
        int value = Integer.parseInt(commands[3]);
        try {
            network.addRelation(id1, id2, value);
        } catch (PersonIdNotFoundException e) {
            e.print();
            return;
        } catch (EqualRelationException e) {
            e.print();
            return;
        }
        System.out.println("Ok");
    }

    private void modifyRelation() {
        int id1 = Integer.parseInt(commands[1]);
        int id2 = Integer.parseInt(commands[2]);
        int value = Integer.parseInt(commands[3]);
        try {
            network.modifyRelation(id1, id2, value);
        } catch (PersonIdNotFoundException e) {
            e.print();
            return;
        } catch (EqualPersonIdException e) {
            e.print();
            return;
        } catch (RelationNotFoundException e) {
            e.print();
            return;
        }
        System.out.println("Ok");
    }

    private void addPerson()
            throws InstantiationException, IllegalAccessException,
            IllegalArgumentException, InvocationTargetException {
        int id = Integer.parseInt(commands[1]);
        String name = commands[2];
        int age = Integer.parseInt(commands[3]);
        try {
            network.addPerson(this.personConstructor.newInstance(id, name, age));
        } catch (EqualPersonIdException e) {
            e.print();
            return;
        }
        System.out.println("Ok");
    }

    private void queryBestAcquaintance() {
        int id = Integer.parseInt(commands[1]);
        int ret;
        try {
            ret = network.queryBestAcquaintance(id);
        } catch (PersonIdNotFoundException e) {
            e.print();
            return;
        } catch (AcquaintanceNotFoundException e) {
            e.print();
            return;
        }
        System.out.println(ret);
    }

    private void resolve(Message message) {
        if (message instanceof NoticeMessage) {
            System.out.print("notice: " + ((NoticeMessage) message).getString());
        } else if (message instanceof EmojiMessage) {
            System.out.print("Emoji: " + ((EmojiMessage) message).getEmojiId());
        } else if (message instanceof RedEnvelopeMessage) {
            System.out.print("RedEnvelope: " + ((RedEnvelopeMessage) message).getMoney());
        } else {
            System.out.print("Ordinary message: " + message.getId());
        }

    }

    private void querySocialValue() {
        int id = Integer.parseInt(commands[1]);
        int ret;
        try {
            ret = network.querySocialValue(id);
        } catch (PersonIdNotFoundException e) {
            e.print();
            return;
        }
        System.out.println(ret);
    }

    private void loadNetwork(Scanner sc) {
        int n = Integer.parseInt(commands[1]);
        int[] ids = new int[n];
        String[] names = new String[n];
        int[] ages = new int[n];
        for (int i = 0; i < n; i++) {
            ids[i] = sc.nextInt();
        }
        for (int i = 0; i < n; i++) {
            names[i] = sc.next();
        }
        for (int i = 0; i < n; i++) {
            ages[i] = sc.nextInt();
        }
        for (int i = 0; i < n; i++) {
            try {
                network.addPerson(this.personConstructor.newInstance(
                        ids[i], names[i], ages[i]));
            } catch (Exception e) {
                throw new RuntimeException("Unreachable");
            }
        }
        for (int i = 0; i < n - 1; i++) {
            for (int j = 0; j <= i; j++) {
                int value = sc.nextInt();
                if (value != 0) {
                    try {
                        network.addRelation(ids[i + 1], ids[j], value);
                    } catch (Exception e) {
                        throw new RuntimeException("Unreachable");
                    }
                }
            }
        }
        sc.nextLine();
        System.out.println("Ok");
    }
}
