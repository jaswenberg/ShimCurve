AttachSpec("../CHIMP/CHIMP.spec");
AttachSpec("spec");
Rx<x>:=PolynomialRing(Rationals());

//2-torsion discriminant 15 example
C:=HyperellipticCurve([Polynomial([RationalField() | 781665361785297,
-1598238514840464, -842925344280885, -1665041035386880, 3641112105010635,
-1046862062174064, -124624667875247]), Polynomial([RationalField() |])]);
J:=Jacobian(C);
T:=TorsionSubgroup(J);
assert PrimaryAbelianInvariants(T) eq [2];


prec := 1000;
F := RationalsExtra(prec);
X := ChangeRing(C,F);
_,B:=HeuristicEndomorphismAlgebra(X : CC:=true);
B;
IsQuaternionAlgebra(B);
assert Discriminant(B) eq 15;

_,D:=HeuristicEndomorphismAlgebra(X : Geometric:=false);

/////////////////////////////////////////
//Z/2 x Z/2 BUT has CM!
IgusaClebsch:=[ 8325120, 1182210785280, 3554223225946767360, 35197602656293847939678208 ];
X:=HyperellipticCurveFromIgusaClebsch(ChangeUniverse(IgusaClebsch,Rationals()));
C:=ReducedWamelenModel(X);
C:=HyperellipticCurve([Polynomial([RationalField() | 0, 4225, 0, 16900, 0, 15876]),
Polynomial([RationalField() |])]);
J:=Jacobian(C);
T:=TorsionSubgroup(J);
assert PrimaryAbelianInvariants(T) eq [2,2];

prec := 1000;
F := RationalsExtra(prec);
X := ChangeRing(C,F);
_,B:=HeuristicEndomorphismAlgebra(X : CC:=true);
B;
IsQuaternionAlgebra(B);
Discriminant(B);
_,D:=HeuristicEndomorphismAlgebra(X : Geometric:=false);


////////////////////////////////////////////
//Z/2xZ/2
IgusaClebsch:=[ -20495360/177147, 211980124160/1162261467,
-6035193812756725760/205891132094649, 444335783182947734471523172352/5814973700\
3040059690390169 ];
X:=HyperellipticCurveFromIgusaClebsch(ChangeUniverse(IgusaClebsch,Rationals()));
C:=ReducedWamelenModel(X);
//C:=HyperellipticCurve([Polynomial([RationalField() | 0, 300, 0, -325, -255, -303, -153]), Polynomial([RationalField() |])]);
J:=Jacobian(C);
T:=TorsionSubgroup(J);
assert PrimaryAbelianInvariants(T) eq [2,2];

prec := 1000;
F := RationalsExtra(prec);
X := ChangeRing(C,F);
_,B:=HeuristicEndomorphismAlgebra(X : CC:=true);
B;
tr,D:=IsQuaternionAlgebra(B);
assert tr;
assert Discriminant(D) eq 15;

  X := ChangeRing(C,F);
  _,D:=HeuristicEndomorphismAlgebra(X : Geometric:=false);  
  assert Dimension(D) eq 1;
  Factorization(Conductor(C));

////////////////////////////////////////////////
//Z/6 twist search
IgusaClebsch:=[ 11720704/177147, 452386816000/1162261467, 1046080705789952000/205891132094649,
121749249767092999159808000000/58149737003040059690390169 ];
X:=HyperellipticCurveFromIgusaClebsch(ChangeUniverse(IgusaClebsch,Rationals()));
C:=ReducedWamelenModel(X);

twists:= [ d : d in [-10000..10000] | d ne 0  and IsSquarefree(d) ];
for d in twists do
  Cd:=QuadraticTwist(C,d);
  Td:=TorsionSubgroup(Jacobian(Cd));
  if PrimaryAbelianInvariants(Td) ne [2] then
    d; Cd; Td;
  end if;
end for;


////////////////////////////////////////////////
//(Z/3) twist search
IgusaClebsch:=[ 1085223/64, -121558451625/2048, -232600423418065125/1048576,
8971971396591449621390625/34359738368 ];
X:=HyperellipticCurveFromIgusaClebsch(ChangeUniverse(IgusaClebsch,Rationals()));
C:=ReducedWamelenModel(X);

d:=-31;
Cd:=QuadraticTwist(C,d);
//Cd:=HyperellipticCurve([Polynomial([RationalField() | -641111, 1093308, -1432758, 2596157, 266910, -1634196, 492497]), Polynomial([RationalField() |])]);
Td:=TorsionSubgroup(Jacobian(Cd));
assert PrimaryAbelianInvariants(Td) eq [3];


prec := 1000;
F := RationalsExtra(prec);
X := ChangeRing(Cd,F);
_,B:=HeuristicEndomorphismAlgebra(X : CC:=true);
B;
tr,D:=IsQuaternionAlgebra(B);
assert tr;
assert Discriminant(D) eq 15;

///////////////////////////////

list:=HeuristicNontrivialTorsion("Data/X*(15,1)-curves.m");


for s in list do
  IgusaClebsch:=s`IgusaClebsch;
  X:=HyperellipticCurveFromIgusaClebsch(ChangeUniverse(IgusaClebsch,Rationals()));
  C:=ReducedWamelenModel(X);
  J:=Jacobian(C);
  T:=TorsionSubgroup(J);
  IgusaClebsch;
  s`TorsionHeursiticTwist;
  T;
end for;
