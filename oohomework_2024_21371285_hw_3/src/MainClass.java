import expr.Expr;

import java.util.Scanner;

public class MainClass {
    public static void main(String[] args) {
        Scanner scanner = new Scanner(System.in);
        int n = scanner.nextInt();
        scanner.nextLine();
        while (n > 0) {
            FuncExpander.read(scanner.nextLine());
            n--;
        }
        String input = scanner.nextLine();

        Lexer lexer = new Lexer(input);
        Parser parser = new Parser(lexer);

        Expr expr = parser.parseExpr();
        System.out.print(expr.getPoly().asString(false));
    }
}