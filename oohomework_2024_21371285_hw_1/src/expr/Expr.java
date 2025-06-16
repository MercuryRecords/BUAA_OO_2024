package expr;

import java.math.BigInteger;
import java.util.HashMap;

public class Expr implements Factor {
    private HashMap<String, BigInteger> terms;

    public Expr() {
        this.terms = new HashMap<>();
    }

    public void addTerm(Term term, Boolean sign) {
        HashMap<String, BigInteger> toAddOrSub = term.getPoly();
        for (String pow : toAddOrSub.keySet()) {
            if (this.terms.containsKey(pow)) {
                BigInteger newCoef;
                if (sign) {
                    newCoef = this.terms.get(pow).add(toAddOrSub.get(pow));
                } else {
                    newCoef = this.terms.get(pow).subtract(toAddOrSub.get(pow));
                }
                this.terms.replace(pow, newCoef);
            } else {
                if (sign) {
                    this.terms.put(pow, toAddOrSub.get(pow));
                } else {
                    this.terms.put(pow, toAddOrSub.get(pow).negate());
                }
            }
        }
    }

    @Override
    public HashMap<String, BigInteger> getPoly() {
        return this.terms;
    }

    public void powerTrans(BigInteger exp) {
        if (exp.equals(BigInteger.ZERO)) {
            HashMap<String, BigInteger> res = new HashMap<>();
            res.put("0", BigInteger.ONE);
            this.terms = res;
        } else {
            int pow = exp.intValue();
            HashMap<String, BigInteger> base = new HashMap<>(this.terms);
            HashMap<String, BigInteger> toMulti = new HashMap<>(this.terms);
            for (int i = 2; i <= pow; i++) {
                HashMap<String, BigInteger> res = new HashMap<>();
                for (String p1 : base.keySet()) {
                    for (String p2 : toMulti.keySet()) {
                        String newPow = String.valueOf(new BigInteger(p1).add(new BigInteger(p2)));
                        BigInteger newCoef;
                        newCoef = base.get(p1).multiply(toMulti.get(p2));
                        if (!res.containsKey(newPow)) {
                            res.put(newPow, newCoef);
                        } else {
                            BigInteger oldCoef = res.get(newPow);
                            res.replace(newPow, oldCoef.add(newCoef));
                        }
                    }
                }
                base = new HashMap<>(res);
            }
            this.terms = base;
        }
    }

    public String show() {
        String hasAPositiveCoef = null;
        for (String pow : this.terms.keySet()) {
            BigInteger coef = this.terms.get(pow);
            if (coef.compareTo(BigInteger.ZERO) > 0) {
                hasAPositiveCoef = pow;
                break;
            }
        }
        StringBuilder sb = new StringBuilder();
        boolean first = true;
        if (hasAPositiveCoef != null) {
            BigInteger coef = this.terms.get(hasAPositiveCoef);
            if (!(!hasAPositiveCoef.equals("0") && coef.equals(BigInteger.ONE))) {
                sb.append(coef);
                if (!hasAPositiveCoef.equals("0")) {
                    sb.append("*");
                }
            }
            if (!hasAPositiveCoef.equals("0")) {
                sb.append("x");
                if (!hasAPositiveCoef.equals("1")) {
                    sb.append("^");
                    sb.append(hasAPositiveCoef);
                }
            }
            first = false;
        }
        for (String pow : this.terms.keySet()) {
            BigInteger coef = this.terms.get(pow);
            if (coef.equals(BigInteger.ZERO) || pow.equals(hasAPositiveCoef)) { // 0项
                continue;
            } else if (coef.compareTo(BigInteger.ZERO) > 0) { // 正数
                if (!first) {
                    sb.append("+");
                }
            } else {
                sb.append("-");
                coef = coef.negate();
            }
            if (!(!pow.equals("0") && coef.equals(BigInteger.ONE))) {
                sb.append(coef);
                if (!pow.equals("0")) {
                    sb.append("*");
                }
            }
            if (!pow.equals("0")) {
                sb.append("x");
                if (!pow.equals("1")) {
                    sb.append("^");
                    sb.append(pow);
                }
            }
            first = false;
        }
        if (sb.length() == 0) {
            sb.append("0");
        }
        return sb.toString();
    }
}
