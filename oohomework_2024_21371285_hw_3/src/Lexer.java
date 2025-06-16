public class Lexer {
    private final String input;
    private int pos = 0;
    private String curToken;

    public Lexer(String input) {
        this.input = input.replaceAll("[\\s\\t]+", "");
        this.next();
    }

    public String peek() {
        return this.curToken;
    }

    public void next() {
        if (pos == input.length()) {
            return;
        }

        char c = input.charAt(pos);
        if (Character.isDigit(c)) {
            curToken = this.getNumber();
        } else if (c == 'e') {
            curToken = this.getExpFunc();
        } else if (c == 'd') {
            pos += 3;
            curToken = "dx";
        } else {
            pos += 1;
            curToken = String.valueOf(c);
        }
    }


    public boolean isSign() {
        return (this.curToken.equals("+") || this.curToken.equals("-"));
    }

    public boolean isNumber() {
        return Character.isDigit(this.peek().charAt(0));
    }

    private String getNumber() {
        StringBuilder sb = new StringBuilder();
        while (pos < input.length() && Character.isDigit(input.charAt(pos))) {
            sb.append(input.charAt(pos));
            ++pos;
        }

        return sb.toString();
    }

    private String getExpFunc() {
        pos = pos + 4;
        return "exp";
    }
}
