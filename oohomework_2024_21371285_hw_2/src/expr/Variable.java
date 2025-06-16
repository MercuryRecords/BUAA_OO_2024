package expr;

import java.math.BigInteger;

public class Variable {
    private final BigInteger exp;

    public Variable(BigInteger exp) {
        this.exp = exp;
    }

    public BigInteger getPower() {
        return this.exp;
    }
}
