/* A curve over a number field built the documented way (BaseNumberFieldExtra)
 * and through a plain NumberField (CurveExtra) must give the same algebra over
 * the base. Before the CurveExtra fix the second route descended to QQ.
 *
 * Both routes run at the same precision, the fields include a non-Galois cubic
 * one (where the choice of embedding matters), and one case is pinned to a
 * known answer so that the test cannot pass with both routes equally wrong:
 * y^2 = x^6 + 1 has Jacobian isogenous to E x E with E : y^2 = x^3 + 1 (CM by
 * QQ(sqrt -3)), so End^0 over any K not containing sqrt -3 is M_2(QQ) (one
 * component, m = 2 over a field of degree 1) and over QQbar it is
 * M_2(QQ(sqrt -3)) (m = 2 over a field of degree 2). */

prec := 300;
R<t> := PolynomialRing(Rationals());
for pol in [t^2 - 5, t^2 - t + 1, t^2 + 2, t^3 - t + 1] do
    F<r> := BaseNumberFieldExtra(pol, prec);
    S<x> := PolynomialRing(F);
    K := NumberField(pol); SK<y> := PolynomialRing(K);
    for f in [ x^5 + r*x^3 + x, x^6 + r, x^6 + r*x^4 + x^2 + 1, x^6 + 1 ] do
        descA := HeuristicEndomorphismAlgebra(HyperellipticCurve(f));
        g := SK ! [ K ! Eltseq(c) : c in Eltseq(f) ];
        X := CurveExtra(HyperellipticCurve(g) : prec := prec);
        assert BaseRing(X)`base eq BaseRing(X);
        descA2 := HeuristicEndomorphismAlgebra(X);
        print pol, f, descA[2] eq descA2[2];
        assert descA[2] eq descA2[2];
        if f eq x^6 + 1 then
            /* M_2(QQ) over K, except over QQ(zeta_3) = QQ(sqrt -3), where the CM is defined: M_2(QQ(sqrt -3)) */
            dimD := IsSquare(K ! -3) select 2 else 1;
            assert #descA2[2] eq 1 and descA2[2][1][1] eq 2 and descA2[2][1][2] eq dimD;
            descG := HeuristicEndomorphismAlgebra(X : Geometric := true);
            assert #descG[2] eq 1 and descG[2][1][1] eq 2 and descG[2][1][2] eq 2;       // M_2(CM) over QQbar
        end if;
    end for;
end for;
print "Test-CurveExtra: all passed";
