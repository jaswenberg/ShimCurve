_<x> := PolynomialRing(Rationals());

myfunc := function(t);
  try
    X := IntegralModel(HyperellipticCurve(x^5 + 8*x^4 + t*x^3 + 16*x^2 - 4*x));
    d := t^2-432;
    d := Abs(2*3*Numerator(d)*Denominator(d));
    for r in Divisors(d) do
      if not IsSquarefree(r) then continue; end if;
      for rs in [-r,r] do
        ab := AbelianInvariants(TorsionSubgroup(Jacobian(QuadraticTwist(X,rs))));
        if ab ne [2] then
          print t, rs, ab;
        end if;
      end for;
    end for;
  catch e;
    print t, e;
  end try;
  return t, [];
end function;

for bnd := 100 to 1000 do
  b := bnd;
  for a in [-bnd..bnd] do
    if Gcd(a,b) gt 1 then continue; end if;
    myfunc(a/b);
  end for;
  
  for a in [-bnd,bnd] do
    for b in [1..bnd] do
      if Gcd(a,b) gt 1 then continue; end if;
      myfunc(a/b);
    end for;
  end for;
end for;
