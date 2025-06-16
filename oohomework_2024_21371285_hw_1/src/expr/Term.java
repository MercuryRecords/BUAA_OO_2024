package expr;

import java.math.BigInteger;
import java.util.HashMap;

public class Term implements Factor {
    private HashMap<String, BigInteger> factors;

    public Term() {
        this.factors = new HashMap<>();
        this.factors.put("0", BigInteger.ONE);
    }

    public void addFactor(Factor factor, Boolean sign) {
        HashMap<String, BigInteger> toMulti = factor.getPoly();
        HashMap<String, BigInteger> res = new HashMap<>();
        for (String pow1 : this.factors.keySet()) {
            for (String pow2 : toMulti.keySet()) {
                String newPow = String.valueOf(new BigInteger(pow1).add(new BigInteger(pow2)));
                BigInteger newCoef;
                if (sign) {
                    newCoef = this.factors.get(pow1).multiply(toMulti.get(pow2));
                } else {
                    newCoef = this.factors.get(pow1).multiply(toMulti.get(pow2)).negate();
                }
                if (!res.containsKey(newPow)) {
                    res.put(newPow, newCoef);
                } else {
                    BigInteger oldCoef = res.get(newPow);
                    res.replace(newPow, oldCoef.add(newCoef));
                }
            }
        }
        this.factors = res;
    }

    @Override
    public HashMap<String, BigInteger> getPoly() {
        return this.factors;
    }

    public void powerTrans(BigInteger exp) {
        if (exp.equals(BigInteger.ZERO)) {
            HashMap<String, BigInteger> res = new HashMap<>();
            res.put("0", BigInteger.ONE);
            this.factors = res;
        } else {
            int pow = exp.intValue();
            HashMap<String, BigInteger> base = new HashMap<>(this.factors);
            HashMap<String, BigInteger> toMulti = new HashMap<>(this.factors);
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
                            res.replace(newPow, oldCoef.multiply(newCoef));
                        }
                    }
                }
                base = new HashMap<>(res);
            }
            this.factors = base;
        }
    }
}
