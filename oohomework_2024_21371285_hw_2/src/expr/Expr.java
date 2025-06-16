package expr;

import java.math.BigInteger;

public class Expr {
    private Poly po;

    public Expr() {
        this.po = new Poly();
    }

    public void addTerm(Term term, Boolean sign) {
        Poly toAdd = term.getPoly();
        if (!sign) {
            toAdd.negate();
        }
        for (Mono mono: toAdd.getMos().keySet()) {
            this.po.add(mono);
        }
    }

    public void powerTrans(BigInteger exp) {
        this.po.powerTrans(exp);
    }

    public Poly getPoly() {
        return this.po;
    }
}
