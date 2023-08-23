SetColumns(0);

intrinsic PointsCardinalityTwistsFiniteField(IgusaClebschModp::SeqEnum) -> SeqEnum
  {Given Igusa-Clebsch invariants over a finite field F_p,
   create a genus 2 curve from these invariants defined over F_p.
    Return the point count of the Jacobian of this curve and its twist}

  Rx<x>:=PolynomialRing(Integers());
  assert Characteristic(Universe(IgusaClebschModp)) gt 0;
  Cp:=HyperellipticCurveFromIgusaClebsch(IgusaClebschModp);
  assert BaseRing(Cp) eq Universe(IgusaClebschModp);
  Jp:=Jacobian(Cp);
  fp:=Rx!EulerFactor(Jp);
  coefs:=Coefficients(fp);
  if coefs[2] eq 0 and coefs[4] eq 0 then
    gp := coefs[1] - coefs[3]*x^2 + coefs[5]*x^4;
    return [ Evaluate(fp,1), Evaluate(gp,1) ];
  else
    return [ Evaluate(fp,1),Evaluate(fp,-1) ];
  end if;

end intrinsic;




intrinsic IntersectAbelianGroups(A::GrpAb,B::GrpAb) -> GrpAb
  {return the subgroup G of finite abelian groups A and B such that all other subgroups of both are contained in G}
  sort:=function(m,n);
  //m,n must be prime powers
    tr,p,k:=IsPrimePower(m);
    tr,q,l:=IsPrimePower(n);
    if p ne q then 
      return m-n;
    else 
      return l-k;
    end if;
  end function;

  invariantsA :=PrimaryAbelianInvariants(A);
  invariantsB :=PrimaryAbelianInvariants(B);

  invariantsA:=Sort(invariantsA,sort);
  invariantsB:=Sort(invariantsB,sort);

  if #invariantsA - #invariantsB le 0 then 
    shorter:=invariantsA;
    longer:=invariantsB;
  else 
    shorter:=invariantsB;
    longer:=invariantsA;
  end if;

  maximal_sub:=[];
  for i in [1..#shorter] do 
    for j in [i..#longer] do 
      gcd:=GCD(shorter[i],longer[j]);
      if gcd ne 1 then 
        Append(~maximal_sub,gcd);
        break j;
      end if;
    end for;
  end for;

  return AbelianGroup(maximal_sub);
end intrinsic;

intrinsic IntersectAbelianGroups(A::SeqEnum,B::SeqEnum) -> GrpAb
  {return the subgroup G of finite abelian groups A and B such that all other subgroups of both are contained in G}
  return IntersectAbelianGroups(AbelianGroup(A),AbelianGroup(B));
end intrinsic;

/*intrinsic IntersectAbelianGroups(A::GrpAb,B::GrpAb) -> GrpAb
  {return the subgroup G of finite abelian groups A and B such that all other subgroups of both are contained in G}
  subgroupsA:=[ G`subgroup : G in Subgroups(A) ];
  subgroupsB:=[ G`subgroup : G in Subgroups(B) ];

  invariantsA := [ PrimaryAbelianInvariants(G) : G in subgroupsA ];
  invariantsB := [ PrimaryAbelianInvariants(G) : G in subgroupsB ];

  intersect:= Setseq(Set([ invar : invar in invariantsA | invar in invariantsB ]));
  maximal_intersects:=[];
  for H in intersect do
    intersect_exclH := Exclude(intersect,H);
    allsubs_exclH :=Setseq(Set(&cat[ [ PrimaryAbelianInvariants(C`subgroup) : C in Subgroups(AbelianGroup(D)) ] : D in intersect_exclH ]));
    if exists(t){ G : G in allsubs_exclH | H eq G } eq false then
      Append(~maximal_intersects,H); //H;
    end if;
  end for;
  //maximal_intersects;

  assert #maximal_intersects eq 1;
  return AbelianGroup(maximal_intersects[1]);
end intrinsic;*/


intrinsic IsSubgroup(A::GrpAb, B::GrpAb) -> BoolElt
  {Is A a subgroup of B?}
  pA:=PrimaryAbelianInvariants(A);
  pB:=PrimaryAbelianInvariants(B);
  if pA eq [] then 
    return true; 
  elif pB eq [] then 
    return false;
  else 
    C:=IntersectAbelianGroups(A,B);
    pC:=PrimaryAbelianInvariants(C);
    if pC eq pA then 
      return true;
    else 
      return false;
    end if;
  end if;
end intrinsic;


    
 


intrinsic JacobianGroupTwistsFiniteField(Cp::CrvHyp) -> SeqEnum
  {Given C_p over a finite field F_p, return the group of the Jacobian of this curve and its twists}

  assert Characteristic(BaseRing(Cp)) gt 0;
  twists:=Twists(Cp);
  return [ AbelianGroup(Jacobian(X)) : X in twists ];

end intrinsic;



intrinsic JacobianGroupTwistsFiniteField(IgusaClebschModp::SeqEnum) -> SeqEnum
  {Given Igusa-Clebsch invariants over a finite field F_p,
   create a genus 2 curve from these invariants defined over F_p.
    Return the point count of the Jacobian of this curve and its twists}

  assert Characteristic(Universe(IgusaClebschModp)) gt 0;
  Cp:=HyperellipticCurveFromIgusaClebsch(IgusaClebschModp);
  twists:=Twists(Cp);
  abs:=[ AbelianGroup(Jacobian(X)) : X in twists ];
  return abs;

end intrinsic;



intrinsic TorsionGroupHeuristicUpToTwist(IgusaClebsch::SeqEnum:group:=AbelianGroup([1]), bound:=200, exponent:=1) -> RngIntElt
  {Given Igusa-Clebsch invariants which define a curve over a number field, check the biggest possible torsion of the Jacobian.
  This is done by reducing mod p for p up to a bound and up to twist. }

  e:=exponent;
  group_invs:=PrimaryAbelianInvariants(group);
  if Universe(IgusaClebsch) eq Integers() then
    ChangeUniverse(~IgusaClebsch,Rationals());
  end if;
  assert Universe(IgusaClebsch) eq Rationals();
  bad_primes_init:=Setseq(Set([ Denominator(I) : I in IgusaClebsch ] cat [Numerator(IgusaClebsch[4])] cat [2,3,5]));
  badprimes:=PrimeDivisors(&*([ a : a in bad_primes_init | a ne 0 ]));
  primes:=[ a : a in PrimesUpTo(bound) | a notin badprimes ];
  possible_groups:=[];
  IgusaClebschModp:=ChangeUniverse(IgusaClebsch,FiniteField(primes[1]^e));
  all_possible_groups:=JacobianGroupTwistsFiniteField(IgusaClebschModp);
  invs:=Setseq(Set([ PrimaryAbelianInvariants(G) : G in all_possible_groups ]));
  all_possible_groups:=[ AbelianGroup(I) : I in invs ];

  Exclude(~primes,primes[1]);
  flag_subgroup:=true;
  for p in primes do
    IgusaClebschModp:=ChangeUniverse(IgusaClebsch,FiniteField(p^e));
    group_twists:=JacobianGroupTwistsFiniteField(IgusaClebschModp);
    grps:=&cat[ [ IntersectAbelianGroups(A,B) : B in group_twists ] : A in all_possible_groups ];
    invs:=Setseq(Set([ PrimaryAbelianInvariants(G) : G in grps ]));
    all_possible_groups:=[ AbelianGroup(I) : I in invs ];
    if invs eq [ [] ] then
      break p;
    end if;
    if group_invs ne [] then
      for D in all_possible_groups do 
        if not IsSubgroup(group,D) then 
          Exclude(~all_possible_groups,D);
        end if;
      end for;
      if all_possible_groups eq [] then 
        flag_subgroup:=false;
        break p;
      end if;
    end if;
  end for;
  if flag_subgroup eq false then
    return "group not in torsion";
  else
    return all_possible_groups;
  end if;

end intrinsic;


intrinsic TorsionGroupHeuristicUpToTwist(C::CrvHyp:group:=AbelianGroup([1]), bound:=1000) -> RngIntElt
  {Given a hyperelliptic curve C over a number field, check the biggest possible prime power torsion of the Jacobian.
  This is done by reducing mod p for p up to a bound and up to twist.}

  assert Type(BaseRing(C)) eq FldNum;
  K:=BaseRing(C);
  OK:=Integers(K);
  f, h := HyperellipticPolynomials(C);
  cofs := {c : c in Eltseq(h) cat Eltseq(f)};
  group_invs:=PrimaryAbelianInvariants(group);
  bad_p_norm:=Norm(Discriminant(C)*2*OK);
  support := PrimeDivisors(Numerator(bad_p_norm)) cat PrimeDivisors(Denominator(bad_p_norm));
  
  disc := Discriminant(C); // needed to check for good reduction
  // We look at all primes above prime numbers up to 200.
  // We require the ramification index to be less than the residue characteristic minus 1,
  // since this guarantees that the reduction map is injective on torsion.
  // This is needed here and also in Order below.
  cofs := {c : c in Eltseq(h) cat Eltseq(f)};
  pl := &cat[[e[1] : e in Decomposition(OK, p) | e[2] lt p-1] : p in PrimesInInterval(3, bound)];
  // "Good reduction" here includes p-integral coefficients.
  pl := [p : p in pl | Valuation(disc, p) eq 0 and forall{c : c in cofs | Valuation(c, p) ge 0}];
  //Sort(~pl, func<p1, p2 | Norm(p1)-Norm(p2)>);
  //s := 1;
  primes:=pl;
  //primes:=[ Factorization(a*OK)[1,1] : a in PrimesUpTo(bound) | not(PrimeDivisors(Norm(a*OK)) subset support) and IsPrime(Norm(Factorization(a*OK)[1,1])) ];
  //primes:=[ p : p in primes | | Set([Coefficients(C)]) ];
  
  possible_groups:=[];
  Fp, red := ResidueClassField(primes[1]);
  Cp := BaseExtend(C, map<K -> Fp | a :-> red(a)>);
  all_possible_groups:=JacobianGroupTwistsFiniteField(Cp);
  invs:=Setseq(Set([ PrimaryAbelianInvariants(G) : G in all_possible_groups ]));
  all_possible_groups:=[ AbelianGroup(I) : I in invs ];

  Exclude(~primes,primes[1]);
  flag_subgroup:=true;
  for p in primes do 
    Fp, red := ResidueClassField(p);
    Cp := BaseExtend(C, map<K -> Fp | a :-> red(a)>);

    group_twists:=JacobianGroupTwistsFiniteField(Cp); 
    grps:=&cat[ [ IntersectAbelianGroups(A,B) : B in group_twists ] : A in all_possible_groups ];
    invs:=Setseq(Set([ PrimaryAbelianInvariants(G) : G in grps ]));
    all_possible_groups:=[ AbelianGroup(I) : I in invs ];
    if invs eq [ [] ] then
      break p;
    end if;
    if group_invs ne [] then
      for D in all_possible_groups do 
        if not IsSubgroup(group,D) then 
          Exclude(~all_possible_groups,D);
        end if;
      end for;
      if all_possible_groups eq [] then 
        flag_subgroup:=false;
        break p;
      end if;
    end if;
  end for;
 /*     if true notin [ IsSubgroup(group, )]
      if group_invs notin Setseq(Set(&cat[ [ PrimaryAbelianInvariants(C`subgroup) : C in Subgroups(AbelianGroup(D)) ] : D in all_possible_groups ])) then
        flag_subgroup:=false;
        break p;
      end if;
    end if;*/


  if flag_subgroup eq false then
    return Sprintf("group %o not in torsion", group_invs);
  else
    return [ PrimaryAbelianInvariants(G) : G in all_possible_groups ];
  end if;

end intrinsic;



/*
intrinsic TorsionHeuristicUpToTwistDivisibleBy(IgusaClebsch::SeqEnum : bound:=150, primes:=[], divisibleby:=-1) -> RngIntElt
  {Given Igusa-Clebsch invariants which define a curve over Q, check highest power of q that divides
  the cardinality of the point count of the Jacobian. This is done by reducing mod p
  for p up to a bound and up to twist. }

  if Universe(IgusaClebsch) eq Integers() then
    ChangeUniverse(~IgusaClebsch,Rationals());
  end if;
  assert Universe(IgusaClebsch) eq Rationals();
  badprimes:=PrimeDivisors(&*([ Denominator(I) : I in IgusaClebsch ] cat [Numerator(IgusaClebsch[4])])*30);
  all_pointcounts:=[];
  for p in [ a : a in PrimesUpTo(bound) | a notin badprimes ] do
    IgusaClebschModp:=ChangeUniverse(IgusaClebsch,FiniteField(p));
    pointcount_twists:=PointsCardinalityTwistsFiniteField(IgusaClebschModp);
    if divisibleby eq -1 or #primes ne 1 then
      Append(~all_pointcounts,pointcount_twists);
    else
      max:=primes[1]^(Integers()!Maximum([ Valuation(a,primes[1]) : a in pointcount_twists ]));
      if IsDivisibleBy(max,divisibleby) then
        Append(~all_pointcounts,pointcount_twists);
      else
        return 0;
      end if;
    end if;
  end for;

  if primes eq [] then
    primes:=PrimeDivisors(&*(all_pointcounts[1]));
  end if;
  tors:=1;
  for q in primes do
    pointcount_modp:=[];
    for point_count in all_pointcounts do
      max:=Maximum([ Valuation(a,q) : a in point_count ]);
      if max eq 0 then
        Append(~pointcount_modp,max);
        break;
      else
        //[q,max];
        Append(~pointcount_modp,max);
      end if;
    end for;
    min_valuation:=Minimum(pointcount_modp);
    tors:=tors*q^min_valuation;
  end for;
  return tors;

end intrinsic;*/



intrinsic NaiveTorsionSearchTwist(X::CrvHyp, primary_invariants::SeqEnum : bound:=10000) -> CrvHyp
  {}
  d:=1;
  while d lt bound do
    for t in [d,-d] do
      Xd:=QuadraticTwist(X,t);
      if IsSubgroup(AbelianGroup(primary_invariants),TorsionSubgroup(Jacobian(Xd))) then
        return Xd;
      end if;
    end for;
    d:=d+1;
  end while;
  return "no torsion found";
end intrinsic;




/*
PrimesWithTorsionModp(X::CrvHyp, G::GrpAb : bound:=200) -> SeqEnum
  {Up to a bound, give the primes p for which G is a subgroup of the abelian surface mod p}
  group_invs:=PrimaryAbelianInvariants(group);
  if Universe(IgusaClebsch) eq Integers() then
    ChangeUniverse(~IgusaClebsch,Rationals());
  end if;
  assert Universe(IgusaClebsch) eq Rationals();
  badprimes:=PrimeDivisors(&*([ Denominator(I) : I in IgusaClebsch ] cat [Numerator(IgusaClebsch[4])])*30);
  primes:=[ a : a in PrimesUpTo(bound) | a notin badprimes ];
  for p in primes do
    IgusaClebschModp:=ChangeUniverse(IgusaClebsch,FiniteField(p));
    group_twists:=JacobianGroupTwistsFiniteField(IgusaClebschModp);
    Setseq(Set(&cat[ [ PrimaryAbelianInvariants(C`subgroup) : C in Subgroups(AbelianGroup(D)) ] : D in all_possible_groups ]))
*/


/*
intrinsic ReduceWeightedProjectiveSpace(IC::SeqEnum) -> SeqEnum
  {}
  dens:=[ Denominator(a) : a in IC ];
  p:=2;
  pd:=[ Valuation(a,p) : a in dens ];
  [ vs[1] - (vs[1] mod 2), vs[2] mod 4, vs[3] mod 6, vs[4] mod 10 ];
  end intrinsic
*/
