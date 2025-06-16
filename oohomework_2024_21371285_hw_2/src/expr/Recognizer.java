package expr;

public class Recognizer {
    public static boolean isNumber(String input, boolean posOnly) {
        if (input == null) {
            return false;
        }
        int pos = 0;
        if (input.charAt(pos) == '+' || (input.charAt(pos) == '-' && !posOnly)) {
            pos++;
        }
        while (pos < input.length()) {
            if (!Character.isDigit(input.charAt(pos))) {
                return false;
            }
            pos++;
        }
        if (pos == input.length()) {
            return true;
        }
        return false;
    }
    
    public static boolean isPower(String input) {
        if (input == null) {
            return false;
        }
        if (input.charAt(0) == 'x') { // 幂函数
            if (input.length() == 1) {
                return true;
            } else if (input.charAt(1) == '^') {
                return isNumber(input.substring(2), true);
            } else {
                return false;
            }
        }
        return false;
    }

    public static boolean isExponent(String input) {
        if (input == null || input.length() <= 5) {
            return false;
        }
        if (input.startsWith("exp(")) {
            int pos = 4;
            int cnt = 1;
            while (pos < input.length() && cnt > 0) {
                if (input.charAt(pos) == '(') {
                    cnt++;
                } else if (input.charAt(pos) == ')') {
                    cnt--;
                }
                pos++;
            }
            if (pos == input.length()) {
                return true;
            } else if (cnt == 0 && input.charAt(pos) == '^') {
                pos++;
                return isNumber(input.substring(pos), true);
            }
        }
        return false;
    }
}
