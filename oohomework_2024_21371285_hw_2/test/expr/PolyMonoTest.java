package expr;

import org.junit.Test;

import java.math.BigInteger;

public class PolyMonoTest {
    @Test
    public void MonoEqual1() {
        Mono mono1 = new Mono(BigInteger.TEN, BigInteger.ONE, null);
        Mono mono2 = new Mono(BigInteger.ONE, BigInteger.ONE, null);
        System.out.println(mono1.equals(mono2));
    }
    @Test
    public void MonoEqual2() {
        Mono mono1 = new Mono(BigInteger.TEN, BigInteger.ONE, null);
        Mono mono2 = new Mono(BigInteger.ONE, BigInteger.ONE, null);
        Poly poly1 = new Poly(mono1);
        Poly poly2 = new Poly(mono2);

        System.out.println(poly1.equals(poly2));
    }
    @Test
    public void ExponentEqual3() {
        Mono mono1 = new Mono(BigInteger.TEN, BigInteger.ONE, null);
        Mono mono2 = new Mono(BigInteger.ONE, BigInteger.ONE, null);
        Poly poly1 = new Poly(mono1);
        Poly poly2 = new Poly(mono2);
        Mono mono3 = new Mono(poly1);
        Mono mono4 = new Mono(poly2);

        System.out.println(mono3.equals(mono4));
    }

    @Test
    public void PolyAddSame() {
        Mono mono1 = new Mono(BigInteger.TEN, BigInteger.ONE, null);
        Poly poly1 = new Poly(mono1);
        Mono mono2 = new Mono(BigInteger.ONE, BigInteger.ONE, null);
        poly1.add(mono2);

        System.out.println(poly1.getMos().size());
    }

}