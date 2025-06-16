import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Objects;
import java.util.Queue;
import java.util.Scanner;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class TestMain {
    public static void main(String[] args) throws FileNotFoundException {
        File file = new File("E:\\ObjectOriented\\oohomework_2024_21371285_hw_7\\stdin.txt");
        Scanner scanner = new Scanner(file);
        ArrayList<String> lines = new ArrayList<>();
        while (scanner.hasNextLine()) {
            lines.add(scanner.nextLine());
        }
        System.setIn(new TimeInputStream(lines));
        MainClass.main(args);
    }

    private static class Pair<K, V> {
        private final K first;
        private final V second;

        Pair(K first, V second) {
            this.first = first;
            this.second = second;
        }

        public K getFirst() {
            return first;
        }

        public V getSecond() {
            return second;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj) { return true; }
            if (obj == null || getClass() != obj.getClass()) { return false; }
            Pair<?, ?> pair = (Pair<?, ?>) obj;
            return Objects.equals(first, pair.first) && Objects.equals(second, pair.second);
        }

        @Override
        public int hashCode() {
            return Objects.hash(first, second);
        }

        @Override
        public String toString() {
            return "<" + first + ", " + second + ">";
        }
    }

    private static class TimeInputStream extends InputStream {
        private static final Pattern pattern = Pattern.compile("\\[(.*?)](.*)");
        private final Queue<Pair<Long, String>> data = new ArrayDeque<>();
        private final Queue<Integer> cache = new ArrayDeque<>();

        TimeInputStream(ArrayList<String> lines) {
            final long initTime = System.currentTimeMillis();
            for (String line : lines) {
                Matcher matcher = pattern.matcher(line);
                if (matcher.find()) {
                    long time = (long) (Double.parseDouble(matcher.group(1)) * 1000 + 0.5);
                    String content = matcher.group(2);
                    data.add(new Pair<>(initTime + time, content));
                } else {
                    throw new RuntimeException("Invalid input: " + line);
                }
            }
        }

        @Override
        public int read() throws IOException {
            if (cache.isEmpty()) {
                if (data.isEmpty()) { return -1; }
                try {
                    long time = data.peek().getFirst() - System.currentTimeMillis();
                    if (time > 0) { Thread.sleep(time); }
                    String content = Objects.requireNonNull(data.poll()).getSecond();
                    content.chars().forEach(cache::add);
                    cache.add(10);
                } catch (InterruptedException e) {
                    throw new IOException(e);
                }
            }
            return Objects.requireNonNull(cache.poll());
        }

        @Override
        public int read(byte[] b, int off, int len) throws IOException {
            if (b == null) {
                throw new NullPointerException();
            } else if (off < 0 || len < 0 || len > b.length - off) {
                throw new IndexOutOfBoundsException();
            } else if (len == 0) {
                return 0;
            }

            int c = read();
            if (c == -1) { return -1; }
            b[off] = (byte) c;

            int i = 1;
            for (; i < len; i++) {
                if (cache.isEmpty()) { break; }
                c = read();
                if (c == -1) { break; }
                b[off + i] = (byte) c;
            }
            return i;
        }
    }
}