import java.io.BufferedReader;
import java.io.File;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.util.Base64;
import javax.crypto.Cipher;
import javax.crypto.spec.SecretKeySpec;

public class Main {
    private static int[] an_array_of_number;

    private static String[] an_array_of_string;

    static {
        fill_the_number_array();
        fill_the_string_array();
    }

    private static void fill_the_number_array() {
        an_array_of_number = new int[4];
        an_array_of_number[0] = (22 ^ 63 ^ 175 ^ 199) & (184 ^ 150 ^ 55 ^ 88 ^ -" ".length()); // 0
        an_array_of_number[1] = " ".length();   // 1
        an_array_of_number[2] = "  ".length();  // 2
        an_array_of_number[3] = "   ".length(); // 3
    }

    private static void fill_the_string_array() {
        an_array_of_string = new String[an_array_of_number[3]];
        an_array_of_string[an_array_of_number[0]] = string_process_method_1("YTsAJRFhJhwtBmE3HycbJA==", "NSoHt");
        an_array_of_string[an_array_of_number[1]] = string_process_method_1("IwQ9SUY0A29ESw==", "WeOik");
        an_array_of_string[an_array_of_number[2]] = string_process_method_2("EBTlOtafYRI=", "fdECn");
    }

    private static boolean judge_var0_is_null(Object var0) {
        return var0 != null;
    }

    private static boolean judge_var0_less_than_var1(int var0, int var1) {
        return var0 < var1;
    }

    public static void main(String[] args) {
        File file = new File(an_array_of_string[an_array_of_number[0]]);

        try {
            Process process = Runtime.getRuntime().exec(an_array_of_string[an_array_of_number[1]] + file.getAbsolutePath());
            BufferedReader bufferedReader = new BufferedReader(new InputStreamReader(process.getInputStream()));
            String string;
            while (true) {
                if (!judge_var0_is_null(string = bufferedReader.readLine())) {
                    process.waitFor();
                    break;
                }

                System.out.println(string);
            }
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    private static String string_process_method_1(String stringA, String stringB) {
        stringA = new String(Base64.getDecoder().decode(stringA.getBytes(StandardCharsets.UTF_8)), StandardCharsets.UTF_8);
        StringBuilder stringBuilder = new StringBuilder();
        char[] stringBCharArray = stringB.toCharArray();
        int zero = an_array_of_number[0];
        char[] stringACharArray = stringA.toCharArray();
        int stringALength = stringACharArray.length;
        int another_zero = an_array_of_number[0];

        do {
            if (!judge_var0_less_than_var1(another_zero, stringALength)) {
                return String.valueOf(stringBuilder);
            }

            char stringAFirstCharacter = stringACharArray[another_zero];
            stringBuilder.append((char) (stringAFirstCharacter ^ stringBCharArray[zero % stringBCharArray.length]));
            ++zero;
            ++another_zero;
        } while (true);
    }

    private static String string_process_method_2(String stringA, String stringB) {
        try {
            SecretKeySpec keySpec = new SecretKeySpec(MessageDigest.getInstance("MD5").digest(stringB.getBytes(StandardCharsets.UTF_8)), "Blowfish");
            Cipher cipher = Cipher.getInstance("Blowfish");
            cipher.init(an_array_of_number[2], keySpec);
            return new String(cipher.doFinal(Base64.getDecoder().decode(stringA.getBytes(StandardCharsets.UTF_8))), StandardCharsets.UTF_8);
        } catch (Exception e) {
            e.printStackTrace();
            return null;
        }
    }
}
