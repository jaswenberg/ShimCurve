

 
t:=101;

Rx<x>:=PolynomialRing(Rationals());
f:=x^5 + 8*x^4 + t*x^3 + 16*x^2-4*x;
C:=HyperellipticCurve(f);

L:=OptimizedRepresentation(HeuristicEndomorphismFieldOfDefinition(C));
assert GroupName(GaloisGroup(L)) eq "D6";

QA2:=OptimizedRepresentation(SplittingField(f));
assert GroupName(GaloisGroup(QA2)) eq "S4";

LA2:=AbsoluteField(Compositum(L,QA2));
assert Degree(LA2) eq 48;
LandQA2:=L meet QA2;
assert GroupName(GaloisGroup(LandQA2)) eq "S3";

assert IsSubfield(L,QA2) eq false; 



////////////////////////////////
//this finds the mod 2 image by showing it's conjugate to a particular subgroup of the enhanced semidirect product
B<i,j>:=QuaternionAlgebra< Rationals() | -1,3 >;
O:=QuaternionOrder([1,i,j,i*j]);

mu:=(3*i+j-i*j)/6;
z6:=B!(1/2+3*mu);
chi:=B!(i-i*j);

//AutmuO:=[ (1+z6)^l*chi^k : l in [0..5], k in [0..1] ];
//AutmuO:=Setseq(Set(AutmuO));

//ker:= [ [l,k] : l in [0..5], k in [0..1] | GL(4,ResidueClassRing(2))!1 eq NormalizingElementToGL4modN((1+z6)^l*chi^k,O,2) ];

AutmuO:=Aut(O,mu);

G,Gelts:=EnhancedImageGL4(AutmuO,O,2);
subs:=Subgroups(G);


mod2rep:=mod2Galoisimage(C);


Ocirc:=EnhancedSemidirectProduct(O);
EnhancedElementInGL4(Ocirc!<B!1,O!1>);
m1:=EnhancedElementInGL4modN(Ocirc!<B!(1+z6),O!i>, 2);
m2:=EnhancedElementInGL4modN(Ocirc!<B!(1+z6),O!j>, 2);
m3:=EnhancedElementInGL4modN(Ocirc!<B!(chi),O!i>, 2);
m4:=EnhancedElementInGL4modN(Ocirc!<B!(chi),O!j>, 2);


matrix_gens:=[ ChangeRing(a,GF(2)) : a in [m1,m2,m3,m4] ];

HH:=sub< GL(4,GF(2)) | matrix_gens >;
IsGLConjugate(mod2rep,HH);


Hmods:=[ H : H in subs | H`order eq 24 ];
Hmods_subgroup:=[ ChangeRing(H`subgroup,GF(2)) : H in Hmods ];
[ FixedSubspace(H`subgroup) : H in Hmods ];

assert IsGLConjugate(mod2rep,Hmods_subgroup[2]);
assert not(IsGLConjugate(mod2rep,Hmods_subgroup[1]));
assert not(IsGLConjugate(mod2rep,Hmods_subgroup[3]));

Hcorrect:=Hmods_subgroup[2];

enhanced_elts:=[ g`enhanced : g in Gelts ];

Hi:=[ a : a in Gelts | Sprint(a`enhanced) eq "<1, [0 1 0 0]>" ][1];
Hj:=[ a : a in Gelts | Sprint(a`enhanced) eq "<1, [0 0 1 0]>" ][1];
Hij:=[ a : a in Gelts | Sprint(a`enhanced) eq "<1, [0 0 0 1]>" ][1];

ChangeRing(Hi`GL4,GF(2)) in Hcorrect;
ChangeRing(Hj`GL4,GF(2)) in Hcorrect;
ChangeRing(Hij`GL4,GF(2)) in Hcorrect;


inH:=[ a : a in Gelts | ChangeRing(a`GL4,GF(2)) in Hcorrect ];
inHenhanced:=[ a`enhanced : a in inH ];






///////////////////////////////////////////////////
//This uses Shiva's code to compute the mod 4 image.

//G4:=find_mod4image(C);
H4:=MatrixGroup<4, IntegerRing(4) |
Matrix(IntegerRing(4), 4, 4, [ 0, 2, 2, 1, 2, 1, 2, 2, 2, 2, 3, 0, 1, 0, 2, 0 ]),
Matrix(IntegerRing(4), 4, 4, [ 2, 2, 0, 3, 0, 3, 1, 3, 2, 0, 1, 0, 1, 2, 3, 1 ]),
Matrix(IntegerRing(4), 4, 4, [ 0, 2, 0, 1, 0, 3, 2, 0, 2, 3, 1, 2, 3, 2, 0, 0 ]),
Matrix(IntegerRing(4), 4, 4, [ 3, 2, 1, 1, 3, 2, 2, 3, 3, 1, 0, 0, 3, 3, 3, 3 ]),
Matrix(IntegerRing(4), 4, 4, [ 1, 2, 0, 2, 0, 1, 0, 0, 0, 2, 1, 2, 2, 0, 0, 1 ]),
Matrix(IntegerRing(4), 4, 4, [ 1, 2, 0, 0, 0, 3, 0, 0, 0, 0, 3, 2, 0, 0, 0, 1 ]),
Matrix(IntegerRing(4), 4, 4, [ 1, 0, 2, 0, 2, 1, 0, 2, 2, 0, 1, 0, 0, 2, 2, 1 ]),
ScalarMatrix(IntegerRing(4), 4, 3),
Matrix(IntegerRing(4), 4, 4, [ 1, 2, 0, 0, 0, 1, 0, 0, 2, 0, 1, 2, 0, 2, 0, 1 ]) >;


H4transpose:=MatrixGroup< 4, IntegerRing(4) | [Transpose(A) : A in Generators(H4)] >;
FixedSubspace(H4transpose); //(Z/2)



