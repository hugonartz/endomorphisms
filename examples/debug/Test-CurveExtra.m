/* A curve over a number field built the documented way (BaseNumberFieldExtra)
 * and through a plain NumberField (CurveExtra) must give the same algebra over
 * the base. Before the CurveExtra fix the second route descended to QQ. */

prec := 300;
R<t> := PolynomialRing(Rationals());
for pol in [t^2 - 5, t^2 - t + 1, t^2 + 2] do
    F<r> := BaseNumberFieldExtra(pol, prec);
    S<x> := PolynomialRing(F);
    for f in [ x^5 + r*x^3 + x, x^6 + r, x^6 + r*x^4 + x^2 + 1 ] do
        descA := HeuristicEndomorphismAlgebra(HyperellipticCurve(f));
        K := NumberField(pol); SK<y> := PolynomialRing(K);
        g := SK ! [ K ! Eltseq(c) : c in Eltseq(f) ];
        descA2 := HeuristicEndomorphismAlgebra(HyperellipticCurve(g));
        print pol, f, descA[2] eq descA2[2];
        assert descA[2] eq descA2[2];
    end for;
end for;
