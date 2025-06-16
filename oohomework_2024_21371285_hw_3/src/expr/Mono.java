package expr;

import java.math.BigInteger;
import java.util.Objects;

public class Mono {
    private BigInteger coef;
    private BigInteger power;
    private Poly exponent;

    public Mono(BigInteger coef, BigInteger power, Poly exponent) {
        this.coef = coef;
        this.power = power;
        this.exponent = exponent;
    }

    public Mono(Number num) {
        this.coef = num.getCoef();
        this.power = BigInteger.ZERO;
        this.exponent = null;
    }

    public Mono(Variable var) {
        this.coef = BigInteger.ONE;
        this.power = var.getPower();
        this.exponent = null;
    }

    public Mono(Poly exponent) {
        this.coef = BigInteger.ONE;
        this.power = BigInteger.ZERO;
        this.exponent = exponent;
    }

    public Mono(Mono toCopy) {
        this.coef = toCopy.coef;
        this.power = toCopy.power;
        if (toCopy.exponent == null || toCopy.exponent.isEmpty()) {
            this.exponent = null;
            return;
        }
        this.exponent = new Poly(toCopy.exponent);
    }

    public BigInteger getCoef() {
        return this.coef;
    }

    public void setCoef(BigInteger newCoef) {
        this.coef = newCoef;
    }

    public void negate() {
        this.coef = this.coef.negate();
    }

    public Mono multi(Mono monoToMulti) {
        Mono tmpMono = new Mono(monoToMulti);
        BigInteger newCoef = tmpMono.coef.multiply(this.coef);
        if (newCoef.equals(BigInteger.ZERO)) {
            return new Mono(new Number(BigInteger.ZERO, true));
        }
        BigInteger newPower = tmpMono.power.add(this.power);
        Poly newExp;
        if (this.exponent == null && tmpMono.exponent == null) { // 这样写或许可以减少递归深度
            newExp = null;
        } else if (this.exponent == null) {
            newExp = new Poly(tmpMono.exponent);
        } else if (tmpMono.exponent == null) {
            newExp = new Poly(this.exponent);
        } else {
            newExp = new Poly(this.exponent);
            for (Mono monoToAdd : tmpMono.exponent.getMos().keySet()) {
                newExp.add(monoToAdd);
            }
        }
        return new Mono(newCoef, newPower, newExp);
    }

    public Mono multi(BigInteger toMulti) {
        BigInteger coef = this.coef.multiply(toMulti);
        if (coef.equals(BigInteger.ZERO)) {
            return null;
        }
        Mono ret = new Mono(this);
        ret.setCoef(coef);
        return ret;
    }

    public String toString() {
        StringBuilder sb = new StringBuilder();
        if (this.coef.equals(BigInteger.ZERO)) {
            return sb.toString(); // 让Poly决定要不要加0
        }
        sb.append(this.coef);
        boolean hasCoef = true;
        if (this.coef.abs().equals(BigInteger.ONE) &&
            (!this.power.equals(BigInteger.ZERO) ||
            (exponent != null && !exponent.isEmpty()))) { // 省略1
            sb.deleteCharAt(sb.length() - 1);
            hasCoef = false;
        }
        boolean hasPower = false;
        if (!this.power.equals(BigInteger.ZERO)) {
            if (hasCoef) {
                sb.append("*");
            }
            hasPower = true;
            sb.append("x");
            if (!this.power.equals(BigInteger.ONE)) {
                sb.append("^");
                sb.append(this.power);
            }
        }
        if (exponent != null && !exponent.isEmpty()) {
            if (hasPower || hasCoef) {
                sb.append("*");
            }
            String insideExp = exponent.asString(true);
            String[] tmp = insideExp.split("\\*");
            if (canBeTeared(tmp)) {
                sb.append("exp(");
                sb.append(tmp[1], 0, tmp[1].length() - 1);
                sb.append(")^");
                sb.append(tmp[0].substring(1));
            } else {
                sb.append("exp(");
                sb.append(insideExp);
                sb.append(")");
            }
        }
        return sb.toString();
    }

    private boolean canBeTeared(String[] input) {
        if (input.length == 2) {
            if (input[0].charAt(0) == '(' && input[1].charAt(input[1].length() - 1) == ')') {
                if (Recognizer.isNumber(input[0].substring(1), true) && input[1].length() >= 2) {
                    return Recognizer.isPower(input[1].substring(0, input[1].length() - 1)) ||
                           Recognizer.isExponent(input[1].substring(0, input[1].length() - 1));
                }
            }
        }
        return false;
    }

    public boolean isNegative() {
        return this.coef.compareTo(BigInteger.ZERO) < 0;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }
        Mono mono = (Mono) o;
        if (!power.equals(mono.power)) {
            return false;
        }
        if (exponent == null && mono.exponent == null) {
            return true;
        }
        return Objects.equals(exponent, mono.exponent);
    }

    @Override
    public int hashCode() {
        return Objects.hash(power, exponent);
    }

    public Poly derive() {
        if (this.coef.equals(BigInteger.ZERO)) {
            return new Poly();
        }
        else if (power.equals(BigInteger.ZERO) && (exponent == null || exponent.isEmpty())) {
            return new Poly(new Mono(new Number(BigInteger.ZERO, true)));
        } else if (exponent == null || exponent.isEmpty()) {
            Mono mono = new Mono(coef.multiply(power), power.subtract(BigInteger.ONE), null);
            return new Poly(mono);
        } else if (power.equals(BigInteger.ZERO)) {
            Poly toMulti = exponent.derive();
            return new Poly(this).multi(toMulti);
        } else {
            Mono mono1 = new Mono(coef.multiply(power), power.subtract(BigInteger.ONE), exponent);
            Poly toMulti = exponent.derive();
            Poly ret = new Poly(this).multi(toMulti);
            ret.add(mono1);
            return ret;
        }
    }
}
