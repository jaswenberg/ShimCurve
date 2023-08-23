//create igusa clebsch invariants with certain properties like 2-torsion.


Rx<x>:=PolynomialRing(Rationals());
//BelyiMap:=-1/27*(x*(x-3)^2/4);

intrinsic GeneratePQMCurves(D::RngIntElt : endomorphisms:=false, torsion:=true, LinYang:=true, j_list:=[],MestreIsSplit:=false, exponent:=1, BelyiMap:=PolynomialRing(Rationals()).1,size:=1000,WriteToFile:="", global:=false) -> Any
  {}
  Rx<x>:=PolynomialRing(Rationals());
  prec := 500;
  F := RationalsExtra(prec);
  Xbase:=Curve(Parent(BelyiMap));

  if j_list eq [] then
    print "creating js by steadily increasing height";
    height_init:=1;
    small_ht:=Setseq(Set([ a/b : a,b in [-height_init..height_init] | a*b ne 0 ]));

    torsion_jsQ:=[];
    size:=size;
    height:=height_init;
    while #torsion_jsQ lt size do
      height:=height+1;
      extra_a:=[ height/b : b in [-height..height] | b ne 0 and GCD(height,b) eq 1 ];
      extra_b:=[ a/height : a in [-height..height] | a ne 0 and GCD(height,a) eq 1 ];
      extra := extra_a cat extra_b;
      for q in extra do
        j:=BelyiMap(Xbase![q,1]);
        if MestreIsSplit eq false or (MestreIsSplit eq true and MestreObstructionIsSplit(D,j : LinYang:=LinYang)) then  
          IgusaClebsch:=PQMIgusaClebsch(D,j : LinYang:=LinYang);
          if torsion eq true then
            tors_heur:=TorsionGroupHeuristicUpToTwist(IgusaClebsch : bound:=100,exponent:=exponent);
            invr_heur:=< PrimaryAbelianInvariants(gp) : gp in tors_heur >;
            inv:=Sprint(invr_heur);
            if global eq true then 
              C:=HyperellipticCurveFromIgusaClebsch(IgusaClebsch);
              if BaseRing(C) eq Rationals() then 
                X:=ReducedWamelenModel(C);
              else 
                X:=C;
              end if;
              data:=Sprintf("%o||%o",Coefficients(HyperellipticPolynomials(X)),PrimaryAbelianInvariants(TorsionSubgroup(Jacobian(X))));
            else 
              data:=Sprintf("%o||%o",IgusaClebsch, inv); 
            end if;
            data;

            Append(~torsion_jsQ,j);
            if WriteToFile ne "" then 
              PrintFile(WriteToFile,data);
            end if;
          end if;

          if endomorphisms eq true then
            C:=HyperellipticCurveFromIgusaClebsch(IgusaClebsch);
            if BaseRing(C) eq Rationals() then 
              X:=ReducedWamelenModel(C);
            else 
              X:=C;
            end if;
            X;
            XF := ChangeRing(X,F);
            _,B:=HeuristicEndomorphismAlgebra(XF : CC:=true);
            tr,A:=IsQuaternionAlgebra(B);
            printf "The geometric endomorphisms are a quaternion algebra: %o\n",tr;
            if tr then printf "The discriminant of the quaternion algebra is\n %o\n", Discriminant(A); end if;
            _,E:=HeuristicEndomorphismAlgebra(XF : Geometric:=false);
            tr,Efld:=IsNumberField(E);
            if tr then 
              printf "The discriminant of the endomorphisms over the base field (as a number field) is %o\n", SquarefreeFactorization(Discriminant(Efld));
            end if;
            print "============================";
          end if;
        end if;
      end for;
    end while;
  else
    for j in j_list do
      j;
      if MestreIsSplit eq false or (MestreIsSplit eq true and MestreObstructionIsSplit(D,j)) then  
        print "j splits Mestre obstruction";
        IgusaClebsch:=PQMIgusaClebsch(D,j : LinYang:=LinYang);
        //if IgusaClebsch[4] ne 0 then
        C:=HyperellipticCurveFromIgusaClebsch(IgusaClebsch);
        print "Hyperelliptic curve has been computed from Igusa-Clebsch invariants";
        printf "Base ring of C is %o", BaseRing(C);
        if BaseRing(C) eq Rationals() then
          if torsion eq true then
            tors_heur:=TorsionGroupHeuristicUpToTwist(IgusaClebsch : bound:=100);
            invr_heur:=< PrimaryAbelianInvariants(gp) : gp in tors_heur >;
            inv:=Sprint(invr_heur);
            data:=Sprintf("%o|%o",IgusaClebsch, inv); data;
            Append(~torsion_jsQ,j);
            //PrintFile("Data/X*(15,1)-curves.m",data);
          end if;

          if endomorphisms eq true then
            X:=ReducedWamelenModel(C);
            X;
            XF := ChangeRing(X,F);
            _,B:=HeuristicEndomorphismAlgebra(XF : CC:=true);
            B;
            tr,A:=IsQuaternionAlgebra(B);
            printf "The geometric endomorphisms are a quaternion algebra: %o",tr;
            if tr then printf "The discriminant of the quaternion algebra is %o", Discriminant(A); end if;
            _,E:=HeuristicEndomorphismAlgebra(XF : Geometric:=false);
          end if;
        end if;
      end if;
    end for;
  end if;
end intrinsic;


/*AttachSpec("Code/spec");
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
X, phi := BelyiMap(Gamma : prec := 200);*/
