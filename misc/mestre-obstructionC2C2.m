


Rx<x>:=PolynomialRing(Rationals());
//this is phi : X^*(6,P2) -> X^*(6,1)
X := Curve(ProjectiveSpace(PolynomialRing(Rationals(), 2)));
KX<x> := FunctionField(X);
//phi := KX!(32/27*x^3 - 8/9*x - 8/27);

//(Z/2)^2 torsion Belyi map
phi_init := KX!(-108*x^20 + 432*x^16 - 648*x^12 + 432*x^8 - 108*x^4)/(x^24 - 66*x^20 + 1023*x^16 + 2180*x^12 + 1023*x^8 - 66*x^4 + 1);
phi_perms:=[ LFT(phi_init,perm) : perm in Setseq(Permutations({1,2,3})) ];

phi:=phi_perms[4];

num:=Rx!Numerator(phi);
den:=Rx!Denominator(phi);

mestre_a:=(384*x^20 - 1536*x^16 + 2304*x^12 - 1536*x^8 + 384*x^4)/(x^24 + 42*x^20 + 591*x^16 + 2828*x^12 + 591*x^8 + 42*x^4 + 1);
mestre_b:=(-32*x^24 + 2112*x^20 - 32736*x^16 - 69760*x^12 - 32736*x^8 + 2112*x^4 - 32)/(x^24 + 42*x^20 + 591*x^16 + 2828*x^12 + 591*x^8 + 42*x^4 + 1);

num_a:=Rx!384*x^20 - 1536*x^16 + 2304*x^12 - 1536*x^8 + 384*x^4;
den_a:=Rx!x^24 + 42*x^20 + 591*x^16 + 2828*x^12 + 591*x^8 + 42*x^4 + 1;

num_b:=Rx!-32*x^24 + 2112*x^20 - 32736*x^16 - 69760*x^12 - 32736*x^8 + 2112*x^4 - 32;
den_b:=Rx!x^24 + 42*x^20 + 591*x^16 + 2828*x^12 + 591*x^8 + 42*x^4 + 1;

Factorization(num_a);
Factorization(den_a);
Factorization(num_b);
Factorization(den_b);


num_a1:=Rx!6;
den_a1:=Rx!(x^4 - 2*x^3 + 2*x^2 + 2*x + 1)*(x^4 + 2*x^3 + 2*x^2 - 2*x + 1);

num_b1:=Rx!-2;
den_b1:=Rx!(x^4 - 2*x^3 + 2*x^2 + 2*x + 1)*(x^4 + 2*x^3 + 2*x^2 - 2*x + 1);

for v in [20..100] do
  Discriminant(QuaternionAlgebra< Rationals() | Evaluate(num_a,v)/Evaluate(den_a,v), Evaluate(num_b,v)/Evaluate(den_b,v) >);
end for;

for v in [20..100] do
  Discriminant(QuaternionAlgebra< Rationals() | Evaluate(num_a1,v)/Evaluate(den_a1,v), Evaluate(num_b1,v)/Evaluate(den_b1,v) >);
end for;


f:=Rx!(x^4 - 2*x^3 + 2*x^2 + 2*x + 1)*(x^4 + 2*x^3 + 2*x^2 - 2*x + 1);
for v in [20..100] do
  Discriminant(QuaternionAlgebra< Rationals() | -2*Evaluate(f,v), 3 >);
end for;


j:=(-64*x^20 + 256*x^16 - 384*x^12 + 256*x^8 - 64*x^4)/(x^24 + 42*x^20 + 591*x^16 + 2828*x^12 + 591*x^8 + 42*x^4 + 1);
j:=phi;
J2:=12*(j+1);
J4:=6*(j^2+j+1);
J6:=4*(j^3-2*j^2+1);
J8:=(J2*J6-J4^2)/4;
J10:=j^3;
BG6Igusa:=[J2,J4,J6,J8,J10];
C:=HyperellipticCurveFromIgusaInvariants(BG6Igusa);

f,g:=HyperellipticPolynomials(C);
Kz<z>:=Parent(f);
f:=Kz!f
coefs:=Coefficients(f);
fac:=Factorization(f);

f1:=fac[1,1];
f2:=fac[2,1];
f3:=fac[3,1];

assert Discriminant(f1) eq Coefficients(f1)[2]^2 - 4*1*Coefficients(f1)[1];

disc1:=Discriminant(f1);
disc2:=Discriminant(f2);
disc3:=Discriminant(f3);



height_init:=2;
small_ht:=Setseq(Set([ a/b : a,b in [-height_init..height_init] | a*b ne 0 ]));
list:=[];
size:=10;
height:=height_init;
while #list lt size do
  extra_a:=[ height/b : b in [-height..height] | b ne 0 and GCD(height,b) eq 1 ];
  extra_b:=[ a/height : a in [-height..height] | a ne 0 and GCD(height,a) eq 1 ];
  extra := extra_a cat extra_b;
  height:=height+1;
  for q in extra do
    j:=phi(X![q,1]);
    IgusaClebsch:=PQMIgusaClebsch(6,j : LinYang:=false);
    C:=HyperellipticCurveFromIgusaClebsch(IgusaClebsch);
    assert BaseRing(C) eq Rationals();
    j; AB:=TorsionSubgroup(Jacobian(IntegralModel(C)));
    GroupName(AB);
  end for;
end while;


GeneratePQMCurves(6 : endomorphisms:=true, LinYang:=false, MestreIsSplit:=true,BelyiMap:=phi);

