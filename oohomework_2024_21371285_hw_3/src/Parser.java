import expr.Expr;
import expr.Mono;
import expr.Number;
import expr.Poly;
import expr.Term;
import expr.Variable;

import java.math.BigInteger;
import java.util.ArrayList;

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
        Term tmpTerm = parseTerm();
        expr.addTerm(tmpTerm, sign);

        while (lexer.peek().equals("+") || lexer.peek().equals("-")) { // 这里就必须有加减来连接项了，不然应该认为已经结束
            sign = parseSign();
            tmpTerm = parseTerm();
            expr.addTerm(tmpTerm, sign);
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
        Poly tmpFactor = parseFactor();
        term.addFactor(tmpFactor, sign);

        while (lexer.peek().equals("*")) {
            lexer.next();
            tmpFactor = parseFactor();
            term.addFactor(tmpFactor, true);    // 第一个因子之后的因子都认为整体符号为正，若再有符号交给parseFactor处理
        }
        return term;
    }

    public Poly parseFactor() {
        /*
        数字因子 | 表达式因子
        变量因子 | 常数因子 | 表达式因子
        幂函数 | 带符号的整数 |  '(' 表达式 ')' [空白项 指数] | 'exp' 空白项 '(' 空白项 因子 空白项 ')' [空白项 指数] | 自定义函数
         */
        if (lexer.peek().equals("(")) {  // 表达式因子
            // (
            lexer.next();
            Expr expr = parseExpr();
            // )
            lexer.next();
            BigInteger exp = parseExponent();
            expr.powerTrans(exp);
            return expr.getPoly();
        } else if (lexer.peek().equals("x")) { // 幂函数
            lexer.next();
            BigInteger exp = parseExponent();
            return new Poly(new Mono(new Variable(exp)));
        } else if (lexer.isNumber() || lexer.isSign()) { // 常数因子
            Boolean sign = parseSign();
            BigInteger num = new BigInteger(lexer.peek());
            lexer.next();
            return new Poly(new Mono(new Number(num, sign)));
        } else if (lexer.peek().equals("exp")) { // 指数函数
            // (
            lexer.next();
            Poly factor = parseFactor();
            // )
            lexer.next();
            BigInteger exp = parseExponent();
            factor = factor.multi(exp);
            return new Poly(new Mono(factor));
        } else if ("fgh".contains(lexer.peek())) { // 自定义函数调用
            String funcName = lexer.peek();
            lexer.next();
            return parseCustomFunc(funcName);
        } else if (lexer.peek().equals("dx")) { // 求导
            // (
            lexer.next();
            Expr expr = parseExpr();
            // )
            lexer.next();
            return expr.getPoly().derive();
        }
        else {
            return null;
        }
    }

    private Poly parseCustomFunc(String funcName) {
        ArrayList<String> actualParas = new ArrayList<>();
        // (
        lexer.next();
        actualParas.add('(' + parseFactor().asString(false) + ')');

        while (lexer.peek().equals(",")) {
            lexer.next();
            actualParas.add('(' + parseFactor().asString(false) + ')');
        }

        String toParse = FuncExpander.replace(funcName, actualParas);
        Lexer funcLexer = new Lexer(toParse);
        Parser funcParser = new Parser(funcLexer);
        Expr expr = funcParser.parseExpr();

        // )
        lexer.next();

        return expr.getPoly();
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
