package expr;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Objects;

public class Poly {
    private HashMap<Mono, BigInteger> mos;

    public Poly() {
        this.mos = new HashMap<>();
    }

    public Poly(Mono mono) {
        this.mos = new HashMap<>();
        this.mos.put(new Mono(mono), mono.getCoef());
    }

    public Poly(Poly toCopy) {
        this.mos = new HashMap<>();
        if (toCopy == null || toCopy.isEmpty()) {
            return;
        }
        for (Mono mono: toCopy.getMos().keySet()) {
            this.mos.put(new Mono(mono), mono.getCoef());
        }
    }

    public String toString() {
        return asString(false);
    }

    public String asString(boolean asFactor) {
        StringBuilder sb = new StringBuilder();
        boolean first = true;
        Mono firstMono = firstPositive();
        if (firstMono != null && !firstMono.toString().isEmpty()) {
            sb.append(firstMono);
            first = false;
        }
        for (Mono mono: this.mos.keySet()) {
            if (mono.toString().isEmpty() || mono.equals(firstMono)) {
                continue;
            }
            if (!first && !mono.isNegative()) {
                sb.append("+");
            }
            sb.append(mono);
            first = false;
        }
        if (sb.length() == 0) {
            sb.append("0");
        }
        if (asFactor && !canBeSimplified(sb.toString())) {
            sb.insert(0, '(');
            sb.append(')');
        }
        return sb.toString();
    }

    private Mono firstPositive() {
        for (Mono mono: this.mos.keySet()) {
            if (mono.getCoef().compareTo(BigInteger.ZERO) > 0) {
                return mono;
            }
        }
        return null;
    }

    private boolean canBeSimplified(String expr) {
        return Recognizer.isNumber(expr, false) ||
               Recognizer.isPower(expr) ||
                Recognizer.isExponent(expr);
    }

    public HashMap<Mono, BigInteger> getMos() {
        return this.mos;
    }

    public void negate() {
        HashMap<Mono, BigInteger> toReplace = new HashMap<>();
        Iterator<Map.Entry<Mono, BigInteger>> it = this.mos.entrySet().iterator();
        while (it.hasNext()) {
            Map.Entry<Mono, BigInteger> entry = it.next();
            Mono key = entry.getKey();
            key.negate();
            toReplace.put(key, key.getCoef());
            it.remove();
        }
        this.mos = toReplace;
    }
    
    public Poly multi(Poly toMulti) {
        Poly ret = new Poly();
        HashMap<Mono, BigInteger> mulMos = toMulti.getMos();
        for (Mono mono1: mulMos.keySet()) {
            for (Mono mono2: this.mos.keySet()) {
                Mono newMono = mono1.multi(mono2);
                ret.add(newMono);
            }
        }
        return ret;
    }

    public Poly multi(BigInteger toMulti) {
        Poly ret = new Poly();
        for (Mono mono: this.mos.keySet()) {
            ret.add(mono.multi(toMulti));
        }
        return ret;
    }

    public void add(Mono newMono) {
        if (newMono == null) {
            return;
        }
        if (this.mos.containsKey(newMono)) {
            BigInteger newCoef = this.mos.get(newMono);
            newCoef = newCoef.add(newMono.getCoef());
            newMono.setCoef(newCoef);
            this.mos.remove(newMono);
            if (!newCoef.equals(BigInteger.ZERO)) {
                this.mos.put(newMono, newCoef);
            }
        } else {
            this.mos.put(newMono, newMono.getCoef());
        }
        // System.out.println(newMono);
    }

    public void powerTrans(BigInteger exp) {
        if (exp.equals(BigInteger.ZERO)) {
            Mono tmpMono = new Mono(new Number(BigInteger.ONE, true));
            this.mos = new HashMap<>();
            this.add(tmpMono);
            return;
        }
        int pow = exp.intValue();
        HashMap<Mono, BigInteger> base = new HashMap<>();
        Mono tmpMono = new Mono(new Number(BigInteger.ONE, true));
        base.put(tmpMono, tmpMono.getCoef());
        HashMap<Mono, BigInteger> toMulti = new HashMap<>(this.mos);
        for (int i = 1; i <= pow; i++) {
            HashMap<Mono, BigInteger> res = new HashMap<>();
            for (Mono mono1: base.keySet()) {
                for (Mono mono2: toMulti.keySet()) {
                    Mono newMono = mono1.multi(mono2);
                    if (res.containsKey(newMono)) {
                        BigInteger newCoef = res.get(newMono);
                        newCoef = newCoef.add(newMono.getCoef());
                        newMono.setCoef(newCoef);
                        res.remove(newMono);
                        if (!newCoef.equals(BigInteger.ZERO)) {
                            res.put(newMono, newCoef);
                        }
                    } else {
                        res.put(newMono, newMono.getCoef());
                    }
                    // res.put(newMono, newMono.getCoef());
                }
            }
            base = new HashMap<>(res);
        }
        this.mos = base;
    }

    public boolean isEmpty() {
        if (this.mos.isEmpty()) {
            return true;
        }
        for (Mono mono: this.mos.keySet()) { // TODO 或许直接判断coef值
            if (!mono.getCoef().equals(BigInteger.ZERO)) {
                return false;
            }
        }
        return true;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }
        Poly poly = (Poly) o;

        return mos.equals(poly.mos);
    }

    @Override
    public int hashCode() {
        return Objects.hash(mos);
    }
}
