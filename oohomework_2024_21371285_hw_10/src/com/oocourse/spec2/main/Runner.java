package com.oocourse.spec2.main;

import java.io.FileReader;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.util.Scanner;

import com.oocourse.spec2.exceptions.*;

public class Runner {

    private String[] commands;
    private Network network;
    private final Constructor<? extends Person> personConstructor;
    private final Constructor<? extends Network> networkConstructor;
    private final Constructor<? extends Tag> tagConstructor;
    private final Scanner scanner;

    public Runner(Class<? extends Person> personClass, Class<? extends Network> networkClass,
            Class<? extends Tag> tagClass)
            throws NoSuchMethodException, SecurityException {
        personConstructor = personClass.getConstructor(
                int.class, String.class, int.class);
        networkConstructor = networkClass.getConstructor();
        tagConstructor = tagClass.getConstructor(int.class);

        scanner = new Scanner(System.in);
    }

    public void run()
            throws InstantiationException, IllegalAccessException,
            IllegalArgumentException, InvocationTargetException {
        this.network = this.networkConstructor.newInstance();
        while (scanner.hasNextLine()) {
            String cmd = scanner.nextLine();
            // System.out.println("#\t" + cmd);
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
