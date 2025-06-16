import java.util.ArrayList;
import java.util.HashMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class FuncExpander {
    private static HashMap<String, ArrayList<String>> functionParams = new HashMap<>();
    private static HashMap<String, String> functionBodies = new HashMap<>();

    public FuncExpander() {
    }

    public static void read(String input) {
        String funcStatement = input.replaceAll("\\s+", "");

        String funcPattern = "([fgh])\\(([,xyz]*)\\)=(.*)";
        Pattern pattern = Pattern.compile(funcPattern);
        Matcher matcher = pattern.matcher(funcStatement);

        if (matcher.find()) {
            String funcName = matcher.group(1);
            String params = matcher.group(2);
            String body = matcher.group(3);
            body = body.replaceAll("exp", "E");

            ArrayList<String> newParamList = new ArrayList<>();
            for (char param : params.toCharArray()) {
                if (param == 'x' || param == 'y' || param == 'z') {
                    String newItem = "_" + param;
                    body = body.replaceAll(String.valueOf(param), newItem);
                    newParamList.add(newItem);
                }
            }
            functionParams.put(funcName, newParamList);
            functionBodies.put(funcName, body);
        }
    }

    public static String replace(String funcName, ArrayList<String> actualParas) {
        String ret = functionBodies.get(funcName);
        ArrayList<String> formalParas = functionParams.get(funcName);
        int len = formalParas.size();
        for (int i = 0; i < len; i++) {
            ret = ret.replaceAll(formalParas.get(i), actualParas.get(i));
        }
        ret = ret.replaceAll("E", "exp");
        // ret = "(" + ret + ")";
        return ret;
    }
}
