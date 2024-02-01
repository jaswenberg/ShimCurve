
AttachSpec("spec");
=====
sigma := [ Sym(24) |
        (1, 13)(2, 14)(3, 15)(4, 16)(5, 18)(6, 17)(7, 20)(8, 19)(9, 22)(10,
            21)(11, 24)(12, 23),
        (1, 23, 4, 24)(2, 21, 3, 22)(5, 16, 6, 14)(7, 13, 8, 15)(9, 18, 11,
            19)(10, 20, 12, 17),
        (1, 7, 10, 2, 6, 12)(3, 8, 11, 4, 5, 9)(13, 24, 18, 14, 22, 19)(15, 21,
            17, 16, 23, 20)
    ];
SetVerbose("Shimura", true);
Gamma := TriangleSubgroup(sigma);
X, phi := BelyiMap(Gamma : prec := 200);


===============================

I extracted the curve coefficients from the intermediate step, like I
mentioned.  I get the curve:

Rx<x>:=PolynomialRing(Rationals());
X := HyperellipticCurve(Polynomial([1/1728,0,13/432,0,13/36,0,1]));
fX:=Rx!HyperellipticPolynomials(X);
//Factorization(Conductor(X));
auts:=Automorphisms(X);
G:=AutomorphismGroup(X,[auts[4]]);
Xquo:=CurveQuotient(G);

gX:=Rx!x^3 + 13/36*x^2 + 13/432*x + 1/1728;
E:=EllipticCurve([0, 13/36, 0, 13/432, 1/1728]);
assert IsIsomorphic(Xquo,E);

//[ <2, 12>, <3, 3> ]

for d in [ a : a in [-20..-1] cat [1..20] | IsSquarefree(a) ] do
  fXd:=Rx!Evaluate(gX,x^2/d);
  fXd;
  Xd:=HyperellipticCurve(fXd,0);
  Points(IntegralModel(Xd) : Bound:=100);
  F<u,v>:=FunctionField(Xd);
  psi:=iso< Xd -> Xd | [-u,v,1],[-u,v,1] >;
  Ed:=CurveQuotient(AutomorphismGroup(Xd,[psi]));
  Ed;
  IsIsomorphic(E,Ed);
end for;

//testing toby
