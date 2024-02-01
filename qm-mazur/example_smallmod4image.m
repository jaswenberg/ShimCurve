P<x> := PolynomialRing(Rationals());
f1 := x*(x-4352)*(x-6800)*(x-7056)*(x-7225);
f2 := x*(x-4352)*(x-6800)*(x-45968)*(x-71825);
f3 := x*(x-17408)*(x-27200)*(x-28224)*(x-28900);
f4 := x*(x-25857)*(x-65025)*(x-67473)*(x-71825);
f5 := x*(x-39168)*(x-61200)*(x-63504)*(x-65025);
f6 := x*(x-8064)*(x-9464)*(x-12600)*(x-13689);
f7 := x*(x-22400)*(x-24336)*(x-32400)*(x-38025);
f8 := x*(x-32256)*(x-37856)*(x-50400)*(x-54756);

prec := 1000;
F := RationalsExtra(prec);

fs := [f1,f2,f3,f4,f5,f6,f7,f8];
for f in fs do
    C := HyperellipticCurveOfGenus(2,f);
    twotorspol, gens := fourtorsionfield(C : simplified := true);
    print #gens, gens;

    X := ChangeRing(C,F);
    _,B:=HeuristicEndomorphismAlgebra(X : CC:=true);
    B;
    _,D:=HeuristicEndomorphismAlgebra(X : Geometric:=false);
    D;
    L:=HeuristicEndomorphismFieldOfDefinition(X);
    L;

end for;

