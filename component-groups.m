

intrinsic EdixhovenBound(A::GrpAb, p::RngIntElt, t::RngIntElt) -> RngIntElt
  {Given a group G, a residue characteristic p and toric rank t, we compute the
  quantity 'bound'. Suppose an abelian variety is defined is defined over a
  field with charectiristic of residue field = p and prime-to-p part of the
  component group isomorphic to G. Then it must be the case that the unipotent
  rank u is greater than or equal to bound.}
  primes:=PrimeDivisors(Order(A));
  assert p notin primes;
  bound:=0;
  for q in primes do
    if q ne p then
      Ainvp:=Reverse(Sort(pPrimaryInvariants(A,q)));
      if #Ainvp ge t+1 then
        exps := [ Valuation(Ainvp[i],q) : i in [t+1..#Ainvp] ];
        sum:= &+[ (q^Floor(m/2) + q^Ceiling(m/2))/2 -1 : m in exps ];
        bound:=bound+sum;
      end if;
    end if;
  end for;
  return bound;
end intrinsic;
