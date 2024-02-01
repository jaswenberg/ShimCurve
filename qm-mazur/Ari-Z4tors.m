

Rx<x>:=PolynomialRing(Rationals());

height_init:=1;
small_ht:=Setseq(Set([ a/b : a,b in [-height_init..height_init] | a*b ne 0 ]));

torsion_jsQ:=[];
size:=10000000000;
height:=height_init;
while #torsion_jsQ lt size do

  height:=height+1;
  extra_a:=[ height/b : b in [-height..height] | b ne 0 and GCD(height,b) eq 1 ];
  extra_b:=[ a/height : a in [-height..height] | a ne 0 and GCD(height,a) eq 1 ];
  extra := extra_a cat extra_b;
  for a,s in extra do
    d:=a^2-4*s^3;
    f_sd:=(x^2 + 2*s*x - 2*s^2)*(x^4 + 4*s*x^3 + 2*d*x + -s*d);
    if IsHyperellipticCurve([f_sd,0]) then 
      C_sd:=HyperellipticCurve(f_sd);
      tors:=TorsionSubgroup(Jacobian(IntegralModel(C_sd)));
      invs:=PrimaryAbelianInvariants(tors);
      if 4 in invs then 
        f_sd;
        invs;
      end if;
    end if;
  end for;
end while;

 
 
