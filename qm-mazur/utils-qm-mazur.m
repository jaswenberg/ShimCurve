
intrinsic read_data(file::MonStgElt : file_type:="") -> Any
  {read the data file and make into a list with each line a record}


  if file_type eq "defining-equations" then 
    RF := recformat< n : Integers(),
    DefiningEquation,
    EndomorphismField,
    EndomorphismFieldDegree,
    EndomorphismAlgebraDiscriminantOverQ,
    TorsionSubgroupInvariants
     >;
    s := rec< RF | >;
    list:=[];
    lines:=getLines(file);
    for line in lines do
      items:=Split(line,"||");
      s`DefiningEquation:=eval(items[1]);
      s`EndomorphismField:=eval(items[2]);
      s`EndomorphismFieldDegree:=eval(items[3]);
      s`EndomorphismAlgebraDiscriminantOverQ:=eval(items[4]);
      s`TorsionSubgroupInvariants:=eval(items[5]);
      Append(~list,s);
    end for;

    return list;

  else 

    RF := recformat< n : Integers(),
    IgusaClebsch,
    TorsionHeuristicTwist
     >;
    s := rec< RF | >;
    list:=[];
    lines:=getLines(file);
    for line in lines do
      items:=Split(line,"|");
      s`IgusaClebsch:=eval(items[1]);
      s`TorsionHeuristicTwist:=eval(items[2]);
      Append(~list,s);
    end for;

    return list;
    
  end if;
end intrinsic;

intrinsic HeuristicNontrivialTorsion(file::MonStgElt : TorsionGroup:=[]) -> Any
  {return the Igusa Clebsch invariants in file which heuristically might contain TorsionGroup
  as a subgroup.}
  lines:=read_data(file);
  data:=[];
  if TorsionGroup eq [] then
    for s in lines do
      Append(~data,s);
    end for;
  else
    A:=AbelianGroup(TorsionGroup);
    for s in lines do
      possible_tors:=[ AbelianGroup(abinv) : abinv in s`TorsionHeuristicTwist | abinv ne [] ];
      if true in [ IsSubgroup(A,B) : B in possible_tors ] then
        Append(~data,s);
      end if;
    end for;
  end if;
  return data;
end intrinsic;


intrinsic GlobalPQMFromHeuristics(file::MonStgElt : TorsionGroup:=[], bound:=1000, ComputeEndomorphisms:=false, writetofile:="",TwistSearch:=false) -> Any 
  {}
  Rx<x>:=PolynomialRing(Rationals());
  prec := 1000;
  F := RationalsExtra(prec);
  list:=HeuristicNontrivialTorsion(file: TorsionGroup:=TorsionGroup);

  for s in list do
    try 
      IgusaClebsch:=ChangeUniverse(s`IgusaClebsch,Rationals());
      inv:=s`TorsionHeuristicTwist;
      C:=HyperellipticCurveFromIgusaClebsch(IgusaClebsch);
      X:=ReducedWamelenModel(C);
      if TwistSearch eq true then 
        Xtors:=NaiveTorsionSearchTwist(X,TorsionGroup: bound:=bound);
      else 
        Xtors:=X;
      end if;

      if Type(Xtors) eq CrvHyp then
        print "=====================";
        //Factorization(Discriminant(Xtors));
        tors_gp:=PrimaryAbelianInvariants(TorsionSubgroup(Jacobian(Xtors)));
        
        XF := ChangeRing(Xtors,F);
        if ComputeEndomorphisms eq true then 
          _,B:=HeuristicEndomorphismAlgebra(XF : CC:=true);
          tr,D:=IsQuaternionAlgebra(B);
          Discriminant(D);
        end if;

    
        _,E:=HeuristicEndomorphismAlgebra(XF : Geometric:=false);
        _,E:=IsNumberField(E);
        L:=HeuristicEndomorphismFieldOfDefinition(Xtors);
        //assert Degree(L) eq 4;
        pols:=Sprint(Xtors,"Magma");
        fld:= Sprint(DefiningPolynomial(L),"Magma");
        data:=Sprintf("%o||%o||%o||%o||%o",pols, fld,Degree(L),Discriminant(E),tors_gp); data;
        if writetofile ne "" then 
          PrintFile(writetofile,data);
        end if;
      end if;
    catch e
     ;
    end try;
  end for;
  return "";
end intrinsic;