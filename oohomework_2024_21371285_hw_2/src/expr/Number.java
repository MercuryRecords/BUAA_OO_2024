package expr;

import java.math.BigInteger;

public class Number {
    private final BigInteger coef;

    public Number(BigInteger num, Boolean sign) {
        if (sign) {
            this.coef = num;
        } else {
            this.coef = num.negate();
        }
    }

    public BigInteger getCoef() {
        return this.coef;
    }
}
