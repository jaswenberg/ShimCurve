AttachSpec("spec");
AttachSpec("../CHIMP/CHIMP.spec");
Rx<x>:=PolynomialRing(Rationals());
prec := 1000;
F := RationalsExtra(prec);
list:=HeuristicNontrivialTorsion("PQMdata/data/X*(15,1)-curves.m": TorsionGroup:=[3]);

for s in list do
  IgusaClebsch:=ChangeUniverse(s`IgusaClebsch,Rationals());
  inv:=s`TorsionHeuristicTwist;
  C:=HyperellipticCurveFromIgusaClebsch(IgusaClebsch);
  X:=ReducedWamelenModel(C);
  Xtors:=NaiveTorsionSearchTwist(X,[3]: bound:=1000);
  if Type(Xtors) eq CrvHyp then
    print "=====================";
    //Factorization(Discriminant(Xtors));
    tors_gp:=PrimaryAbelianInvariants(TorsionSubgroup(Jacobian(Xtors)));
    XF := ChangeRing(Xtors,F);
    _,B:=HeuristicEndomorphismAlgebra(XF : CC:=true);
    tr,D:=IsQuaternionAlgebra(B);

    if tr then
      assert Discriminant(D) eq 15;
      L:=HeuristicEndomorphismFieldOfDefinition(Xtors);
      //assert Degree(L) eq 4;
      pols:=Sprint(Xtors,"Magma");
      fld:= Sprint(DefiningPolynomial(L),"Magma");
      data:=Sprintf("%o||%o||%o||%o",pols, fld,Degree(L),tors_gp); data;
      PrintFile("X*(15,1)-[3]-definingequations.m",data);
    end if;
  end if;
end for;
