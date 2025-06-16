package expr;

import java.math.BigInteger;

public class Term {
    private Poly po;

    public Term() {
        this.po = new Poly(new Mono(new Number(BigInteger.ONE, true)));
    }

    public void addFactor(Poly polyFactor, Boolean sign) { // poly相乘
        if (polyFactor == null) {
            return;
        }
        if (!sign) {
            polyFactor.negate();
        }

        this.po = polyFactor.multi(this.po);
    }

    public Poly getPoly() {
        return this.po;
    }
}
