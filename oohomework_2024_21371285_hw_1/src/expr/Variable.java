package expr;

import java.math.BigInteger;
import java.util.HashMap;

public class Variable implements Factor {
    private BigInteger pow;

    public Variable(BigInteger pow) {
        this.pow = pow;
    }

    @Override
    public HashMap<String, BigInteger> getPoly() {
        HashMap<String, BigInteger> ret = new HashMap<>();
        ret.put(String.valueOf(this.pow), BigInteger.ONE);
        return ret;
    }

    @Override
    public void powerTrans(BigInteger exp) {
        this.pow = this.pow.multiply(exp);
    }
}
