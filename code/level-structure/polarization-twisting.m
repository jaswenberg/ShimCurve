
  

intrinsic HasPolarizedElementOfDegree(O::AlgQuatOrd,d::RngIntElt) -> BoolElt, AlgQuatElt 
  {return an element mu of O such that mu^2 + d*disc(O) = 0 if it exists.}
  disc:=Discriminant(O);
  B:=QuaternionAlgebra(O);
  Rx<x>:=PolynomialRing(Rationals());
  Em<v>:=NumberField(x^2+d*disc);
  if IsSplittingField(Em,QuaternionAlgebra(O)) then 
    cyc,Czeta,zeta:=IsCyclotomic(Em);
    if cyc eq true then      
      Zzeta:=Integers(Czeta);
      z:=Zzeta.2;
      zO,emb:=Embed(Zzeta,O);
      if CyclotomicOrder(Czeta) eq 4 then 
        assert zO^4 eq 1;
        tr,c:=IsSquare(Integers()!d*disc);
        mu:=c*zO;
        assert mu^2+d*disc eq 0;
        assert mu in O;
        return true, B!mu;
      else 
        assert zO^3 eq 1;
        tr,c:=IsSquare(Integers()!d*disc/3);
        mu:=(2*zO+1)*c;
        assert mu^2+d*disc eq 0;
        assert mu in O;
        return true,B!mu;
      end if;
    else 
      Rm:=Order([1,v]);
      mu,emb:=Embed(Rm,O);
      assert mu^2+d*disc eq 0;
      return true, B!mu;
    end if;
  else 
    return false;
  end if;
end intrinsic;


intrinsic DegreeOfPolarizedElement(O::AlgQuatOrd,mu:AlgQuatOrdElt) -> RngIntElt
  {degree of mu}
  tr,nmu:= IsScalar(mu^2);
  disc:=Discriminant(O);
  del:=SquarefreeFactorization(-nmu/disc);
  assert IsCoercible(Integers(),del);
  assert IsSquarefree(Integers()!del);
  return Integers()!del;
end intrinsic;

intrinsic IsTwisting(O::AlgQuatOrd,mu::AlgQuatElt) -> BoolElt
  {(O,mu) is twisting (of degree del = -mu^2/disc(O)) if there exists chi in O and N_Bx(O)
   such that chi^2 = m, m|Disc(O) and mu*chi = -chi*mu. Return true or false; if true 
   return [mu, chi] up to scaling}

  assert IsMaximal(O);
  Rx<x>:=PolynomialRing(Rationals());
  tr,nmu:= IsScalar(mu^2);
  disc:=Discriminant(O);
  del:=DegreeOfPolarizedElement(O,mu);
  B:=QuaternionAlgebra(O);
  ram:=Divisors(disc);
  //ram:=//Divisors(disc); //cat [ -1*m : m in Divisors(disc) ];

  //the following works for a nice order, so we find a "twisting element" chi
  //for that first and then apply an isomorphism back to O.
  Bdisc:=QuaternionAlgebra(Discriminant(B));
  Odisc:=MaximalOrder(Bdisc);
  for m in ram do
    Bram<i1,j1>:=QuaternionAlgebra< Rationals() | -disc*del, m>;
    if Discriminant(Bram) eq Discriminant(B) then 
      Otwisted:=MaximalOrder(Bram);
      assert i1 in Otwisted and j1 in Otwisted and i1*j1 eq -j1*i1;

      //Bnumfld<i,j>:=QuaternionAlgebra< RationalsAsNumberField() | -disc*del, m>;
      

      break;
    end if;
  end for;

  tr,map:=IsIsomorphic(Bram,B : Isomorphism:=true);
  Otwisted_basis:=[ map(elt) : elt in Basis(Otwisted) ];
  Otwisted_inB:=QuaternionOrder(Otwisted_basis);

  Otwisted_muchi:= [ map(i1), map(j1) ];
  assert Otwisted_muchi[1] in Otwisted_inB and Otwisted_muchi[1] in Otwisted_inB 
    and Otwisted_muchi[1]*Otwisted_muchi[2] eq -Otwisted_muchi[2]*Otwisted_muchi[1];

  //now we have to make them associative orders to retreive the isomorphism
  Bnumfld:=ChangeRing(B,RationalsAsNumberField());
  Onumfld:=Order([ Bnumfld!Eltseq(ChangeRing(b,RationalsAsNumberField())) : b in Basis(O) ]);
  Otwisted_numfld:=Order([ Bnumfld!Eltseq(ChangeRing(b,RationalsAsNumberField())) : b in Basis(Otwisted_inB) ]);
  
  tr,gamma:=IsIsomorphic(Otwisted_numfld,Onumfld : FindElement:=true);
  
  Omuchi_numfld:=[ gamma(Bnumfld!Eltseq(ChangeRing(x,RationalsAsNumberField()))) : x in Otwisted_muchi];
  Omuchi := [ B!Eltseq(ChangeRing(Bnumfld!x,Rationals())) : x in Omuchi_numfld ];

  //make sure its twisting
  assert Omuchi[1]*Omuchi[2] eq -Omuchi[2]*Omuchi[1];
  assert Omuchi[1] eq mu or Omuchi[1] eq -mu;
  assert Omuchi[1] in O;
  assert Omuchi[2] in O;
  assert IsDivisibleBy(disc,Norm(Omuchi[2]));

  return true, [mu,Omuchi[2]];

end intrinsic;




