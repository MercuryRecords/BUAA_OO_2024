package expr;

import java.math.BigInteger;
import java.util.HashMap;

public interface Factor {
    HashMap<String, BigInteger> getPoly();

    void powerTrans(BigInteger exp);
}
