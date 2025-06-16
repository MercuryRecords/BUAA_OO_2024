package expr;

import java.math.BigInteger;
import java.util.HashMap;

public class Number implements Factor {
    private BigInteger num;

    public Number(BigInteger num, Boolean sign) {
        if (sign) {
            this.num = num;
        } else {
            this.num = num.negate();
        }
    }

    public String toString() {
        return this.num.toString();
    }

    @Override
    public HashMap<String, BigInteger> getPoly() {
        HashMap<String, BigInteger> ret = new HashMap<>();
        ret.put("0", this.num);
        return ret;
    }

    @Override
    public void powerTrans(BigInteger exp) {
        this.num = this.num.pow(exp.intValue());
    }
}
