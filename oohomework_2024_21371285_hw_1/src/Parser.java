import expr.Expr;
import expr.Factor;
import expr.Number;
import expr.Term;
import expr.Variable;
import java.math.BigInteger;

public class Parser {
    private final Lexer lexer;

    public Parser(Lexer lexer) {
        this.lexer = lexer;
    }

    public Expr parseExpr() {
        /*
        项 {加 项}
        项 {加减 项}，考虑项的正负性 -> 修改Term.java
        [加减] 项 {加减 项}
        [空白项] [加减] [空白项] 项 [空白项] {加减 空白项 项 空白项}
         */
        Expr expr = new Expr();
        Boolean sign = parseSign();
        expr.addTerm(parseTerm(), sign);

        while (lexer.peek().equals("+") || lexer.peek().equals("-")) { // 这里就必须有加减来连接项了，不然应该认为已经结束
            sign = parseSign();
            expr.addTerm(parseTerm(), sign);
        }
        return expr;
    }

    public Term parseTerm() {
        /*
        因子 {'*' 因子}
        [加减] 因子 {'*' 因子}    // 表达式可以为"- -1 + x ^ 233"
        [加减] [空白项] 因子 [空白项] {'*' 空白项 因子 空白项}
         */
        Term term = new Term();
        Boolean sign = parseSign();
        term.addFactor(parseFactor(), sign);

        while (lexer.peek().equals("*")) {
            lexer.next();
            term.addFactor(parseFactor(), true);    // 第一个因子之后的因子都认为整体符号为正，若再有符号交给parseFactor处理
        }
        return term;
    }

    public Factor parseFactor() {
        /*
        数字因子 | 表达式因子
        变量因子 | 常数因子 | 表达式因子
        幂函数 | 带符号的整数 |  '(' 表达式 ')' [空白项 指数]
         */
        if (lexer.peek().equals("(")) {  // 表达式因子
            // (
            lexer.next();
            Factor expr = parseExpr();
            // )
            lexer.next();
            BigInteger exp = parseExponent();
            expr.powerTrans(exp);
            return expr; // TODO 考虑指数的影响
        } else if (lexer.peek().equals("x")) { // 变量因子
            lexer.next();
            BigInteger exp = parseExponent();
            return new Variable(exp);
        } else { // 常数因子
            Boolean sign = parseSign();
            BigInteger num = new BigInteger(lexer.peek());
            lexer.next();
            return new Number(num, sign);
        }
    }

    public Boolean parseSign() {
        if (lexer.peek().equals("+")) {
            lexer.next();
            return true;
        } else if (lexer.peek().equals("-")) {
            lexer.next();
            return false;
        } else {
            return true;
        }
    }

    public BigInteger parseExponent() {
        if (lexer.peek().equals("^")) {
            lexer.next();
            if (lexer.peek().equals("+")) {
                lexer.next();
            }
            String num = lexer.peek();
            lexer.next();
            // 应该必须是数字了
            return new BigInteger(num);
        } else { // 整体次数为1
            return new BigInteger("1");
        }
    }
}
