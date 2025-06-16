public class Person {
    private final int id;
    private final int to;
    private final int from;

    public Person(int personId, int fromFloor, int toFloor) {
        this.id = personId;
        this.to = toFloor;
        this.from = fromFloor;
    }

    public int getFrom() {
        return this.from;
    }

    public int getTo() {
        return this.to;
    }

    public int getId() {
        return this.id;
    }

    @Override
    public String toString() {
        return id + "-" + from + "-" + to;
    }
}
