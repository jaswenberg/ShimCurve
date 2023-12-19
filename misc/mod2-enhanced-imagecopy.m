

 
prec:=30;
CC:=ComplexField(prec);

Rx<x>:=PolynomialRing(Rationals());
f:=-x^5+4*x^4-10*x^3+8*x^2-2*x;
X:=HyperellipticCurve(f);
X;
XR:=RiemannSurface(f,2 : Precision:=prec);
J:=Jacobian(X);
TwoTorsionSubgroup(J); //(Z/2Z)
HeuristicEndomorphismDescription( X : CC:=true);
//Maximal Order of discriminant 6

QA2:=SplittingField(f);
L:=HeuristicEndomorphismFieldOfDefinition(X);
M:=OptimizedRepresentation(Compositum(QA2,L));
ooplaces:=InfinitePlaces(M);
embC:=ooplaces[1];



XM:=ChangeRing(X,M);
JM:=Jacobian(XM);
TorsM,map2:=TwoTorsionSubgroup(JM);
fM:=ChangeRing(f,M);



frootsM:=[ a[1] : a in Roots(fM)];
frootsC:=[ Evaluate(a,embC) : a in frootsM ];

//2-torsion after applying Abel-Jacobi map
AJ_2tors_basis:=[ AbelJacobi(XR![frootsC[i],0]) : i in [2..5] ];
AJ_2tors_basis_real:= [ RealVector(v) : v in AJ_2tors_basis ];


//Lambda = OmegaZ^2 + Z^2 where Omega = SmallPeriodMatrix()
//This is not the same lattice that the endomorphism package use!
//We embed C^2 --> R^4 to get Lambda in R^4 as a lattice. 
// v=v1+I*v2   v |--> (v1 v2)^T
SPM:=SmallPeriodMatrix(XR);
RR:=RealField(Precision(BaseRing(SPM[1])));
Lambda_basisCC:=[ SPM[1], SPM[2], Parent(SPM[1])![1,0], Parent(SPM[1])![0,1] ];
small_period_matrix:=Transpose(Matrix([ Eltseq(a) : a in Lambda_basisCC ]));
real_basis:=[ RealVector(SPM[1]), RealVector(SPM[2]), 
	RealVector(Parent(SPM[1])![1,0]),RealVector(Parent(SPM[1])![0,1]) ];

real_basis_matrix:=Matrix(RR,[ Eltseq(a) : a in real_basis]);
Lambda:=LatticeWithBasis(real_basis_matrix);

AJ2_lambda:=[ Lambda!Eltseq(2*b) : b in AJ_2tors_basis_real ];
[  Coordinates(b) : b in AJ2_lambda ];
//We see that 2*Q is in the lattice Lambda for each basis element of A[2](C)


C:=BaseRing(AJ_2tors_basis[1]);

//These are the endomorphisms of A(C) in M_2(C)
endos:=HeuristicEndomorphismRepresentation( X : CC:=true);
endosM2:=[ ChangeRing(m[1],CC) : m in endos ];

endosCC:=GeometricEndomorphismRepresentationCC( X );
endosM2CC:=[ ChangeRing(m[1],C) : m in endosCC ];



b1:=Transpose(Matrix(C,1,2,Eltseq(SPM[1])));

//let g = second endomorphism basis in M_2(C) and b = first basis element of Lambda
//Find that g*b \notin Lambda (after embedding in R^4)!?!?
Lambda!Eltseq(RealVector(endosM2[2]*b1));



Pt0:=C![0,0];
AbelJacobi(XR![1,0]);
RationalPoints(C,100);




/////////////////////////////
//test that the endomorphisms preserve the lattice
PM:=PeriodMatrix(X);
BPM:=BigPeriodMatrix(XR);
//assert 2*PM = BPM up to swapping columns

Lambda_basisCC:=Rows(Transpose(BPM));
Lambda_basisCC_mat:=[ Transpose(Matrix(BaseRing(Lambda_basisCC[1]),1,2,Eltseq(v))) : v in Lambda_basisCC ];
real_basis:= [ RealVector(v) : v in Lambda_basisCC ];

real_basis_matrix:=Matrix(RR,[ Eltseq(a) : a in real_basis]);
Lambda:=LatticeWithBasis(real_basis_matrix);

//These are the endomorphisms of A(C) in M_2(C)
endos:=HeuristicEndomorphismRepresentation( X : CC:=true);
endosM2:=[ ChangeRing(m[1],BaseRing(Lambda_basisCC[1])) : m in endos ];

//There's no issue coercing into Lambda, which means that the endomorphisms do indeed preserve the lattice.
[ [ Lambda!Eltseq(RealVector(endo*b)) : b in Lambda_basisCC_mat ] : endo in endosM2 ];



////////////////////////////////
//enumerate A[2](C)


frootsM:=[ a[1] : a in Roots(fM)];
frootsC:=[ Evaluate(a,embC) : a in frootsM ];

//2-torsion after applying Abel-Jacobi map
AJ_2tors_basis:=[ AbelJacobi(XR![frootsC[i],0]) : i in [2..5] ];
AJ_2tors_basis_real:= [ RealVector(v) : v in AJ_2tors_basis ];


LatP:=RealLatticeOfPeriodMatrix(PM);
Latbig:=RealLatticeOfPeriodMatrix(BigPeriodMatrix(XR));

SPM:=SmallPeriodMatrix(XR);
RR:=RealField(Precision(BaseRing(SPM[1])));
Lambda_basisCC:=[ SPM[1], SPM[2], Parent(SPM[1])![1,0], Parent(SPM[1])![0,1] ];
small_period_matrix:=Transpose(Matrix([ Eltseq(a) : a in Lambda_basisCC ]));
Latsmall:=RealLatticeOfPeriodMatrix(small_period_matrix);

//Can only coerce for latsmall
AJ2_lambda:=[ Latsmall!Eltseq(2*b) : b in AJ_2tors_basis_real ];




////////////////////////////////////
//let's map from torus with small period lattice to big

BPM:=ChangeRing(BigPeriodMatrix(XR),CC);
SPM:=ChangeRing(SmallPeriodMatrix(XR),CC);

BPM_basis:=BasisOfBigPeriodMatrix(BPM);
SPM_basis:=BasisOfSmallPeriodMatrix(SPM);

P1:=ColumnSubmatrix(BPM,1,2);
P2:=ColumnSubmatrix(BPM,3,2);

assert ChangeRing(SPM,ComplexField(5)) eq ChangeRing(((P2^-1)*P1)^-1,ComplexField(5));


//BPM=P1*SPM this goes from the lattice defined by the small period matrix to the one defined by the big one.
Latbig:=RealLatticeOfPeriodMatrix(BPM);
[ Latbig!Eltseq(RealVector(P1*SPM_basis[i])) : i in [1..4] ];

Latendo:=RealLatticeOfPeriodMatrix(ChangeRing(PeriodMatrix(X),CC));
assert 2*Latendo eq Latbig;


//Now we create an O/2-basis element for A[2](C) with lattice Latendo.
//First we embed Div(X) -> A(C) using the Abel Jacobi map which has image defined
//by the lattice with the Small Period Matrix.
//Then go from small period matrix to Latendo by multiplying by P1/2

AJ_2tors_basis:=[ AbelJacobi(XR![frootsC[i],0]) : i in [2..5] ];
A2_modlatendo:=[ 1/2*(P1)*Q : Q in AJ_2tors_basis ];
A2_modlatendo_real:=[ RealVector(v) : v in A2_modlatendo ];

//check that they are indeed 2-torsion points.
assert forall(e){ x : x in A2_modlatendo_real | not(IsCoercible(Latendo,Eltseq(x))) };
assert forall(e){ x : x in A2_modlatendo_real | IsCoercible(Latendo,Eltseq(2*x)) };


Q:=A2_modlatendo[1];
a,b,c,d:=Explode(endosM2);
Omod2_elts:=[ (w*a + x*b + y*c + z*d) : w,x,y,z in [0,1] ];
twotorsion_points:=[ a*Q : a in Omod2_elts ];
twotorsion_points_real:= [ RealVector(v) : v in twotorsion_points ];
//this is O_Q: the O-cyclic module generated by Q.


//check that O_Q is all of the two torsion.
assert forall(e){ x : x in twotorsion_points_real | IsCoercible(Latendo,Eltseq(2*x)) };
assert #{ x : x in twotorsion_points_real | IsCoercible(Latendo,Eltseq(x)) } eq 1;


Gal,auts,map:=AutomorphismGroup(M);
Gal_gens:=Setseq(Generators(Gal));

Qsig:=map(Gal_gens[1])(frootsM[2]);
Qsig_modlatendo:=1/2*(P1)*AbelJacobi(XR![Evaluate(Qsig,embC),0]);


assert IsCoercible(Latendo,Eltseq(RealVector(2*Qsig_modlatendo)));
assert 2*Jacobian(XM)![ XM![Qsig,0], XM![0,0] ] eq Identity(Jacobian(XM));

PQsig:=[ i : i in [1..#twotorsion_points] | IsCoercible(Latendo,Eltseq(RealVector(twotorsion_points[i] - Qsig_modlatendo))) ];
assert #PQsig eq 1;
Qsigindex:=PQsig[1];
Omod2Qsig:=Omod2_elts[2];


