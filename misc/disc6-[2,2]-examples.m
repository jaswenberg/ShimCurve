
AttachSpec("spec");
AttachSpec("../CHIMP/CHIMP.spec");

lines:=getLines("../PQMdata/data/X*(6,P2)-[2,2]-definingequations.m");


Rx<x>:=PolynomialRing(Rationals());


prec := 1000;
F := RationalsExtra(prec);


for i in [1..#lines] do 
  line:=lines[i]; 
  f:=Rx!eval(line);
  C:=HyperellipticCurve(f);
  J:=Jacobian(C);
  T:=TorsionSubgroup(J);
  assert PrimaryAbelianInvariants(T) eq [2,2];

  X := ChangeRing(C,F);
  _,D:=HeuristicEndomorphismAlgebra(X : Geometric:=false);  
  assert Dimension(D) eq 2;
  b:=Basis(D)[2];
  
  Discriminant(NumberField(MinimalPolynomial(b)));
  Factorization(Conductor(C));
  J2:=Jacobian(IntegralModel(RichelotIsogenousSurfaces(C)[1]));
  PrimaryAbelianInvariants(TorsionSubgroup(J2));

end for;