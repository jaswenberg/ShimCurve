
load "F2weil_polynomials.m";
load "F3weil_polynomials.m";
load "F5weil_polynomials.m";
load "F7weil_polynomials.m";
Rx<x>:=PolynomialRing(Rationals());

//This functions makes a list the Weil polynomials of QM surfaces over F_q=F_{p^r}.
QMWeilPols:= function(p,r);
  Rx<x>:=PolynomialRing(Integers());
  q:=p^r;
  F:=FiniteField(q);

  //The Weil polynomials are necessarily of this form
  pol_ap1:=[ Rx!(q*x^2+a*x+1)^2 : a in [-Floor(2*Sqrt(q))..Floor(2*Sqrt(q))] | GCD(a,p) eq 1 ];
  pol_reven:=[ Rx!(q*x^2+a*x+1)^2 : a in [0, Sqrt(q), -Sqrt(q), 2*Sqrt(q), -2*Sqrt(q)] | IsEven(r) ];
  pol_rodd:=[ Rx!(q*x^2+a*x+1)^2 : a in [0, p^((r+1)/2), -p^((r+1)/2) ] | IsOdd(r) ];

  qmpols:=pol_ap1 cat pol_reven cat pol_rodd;

  return qmpols;
 end function;

//This is the Weil polynomial base change from F_p to F_p^2
C2:=function(f);
   K<u>:=SplittingField(f);
   Kz<z>:=PolynomialRing(K);
   return Rx!&*[ (1-(1/rt[1]^2)*z)^rt[2] : rt in Roots(Kz!f) ];
end function;

//This is the inverse of C2.
Csqrt:=function(f);

    K:=SplittingField(f);
    Kz<z>:=PolynomialRing(K);
    roots:=Roots(Kz!f);

    E:=K;
    for s in roots do
       if not(IsSquare(E!s[1])) then
           E:=RadicalExtension(E,2,s[1]);
       end if;
     end for;
     E<w>:=AbsoluteField(E);
     Ey<y>:=PolynomialRing(E);

     rts_list:=&cat[ [ E!roots[j,1] : i in [1..roots[j,2]] ] : j in [1..#roots] ];
     sqrt_list_pm:=[ [ (-1)^a*Sqrt(rts_list[1]), (-1)^b*Sqrt(rts_list[2]), (-1)^c*Sqrt(rts_list[3]), (-1)^d*Sqrt(rts_list[4]) ] : a,b,c,d in [0,1] ];
     sqrt_pols:=[ Ey!&*[  (1 - 1/sqrt*y) : sqrt in roots_long ] : roots_long in sqrt_list_pm ];

     Csqrt_list:=[];
     for pol in sqrt_pols do
         try
             Append(~Csqrt_list, Rx!pol);
         catch e
             ;
        end try;
     end for;

  return Setseq(Set(Csqrt_list));
end function;


//This returns the set of all Weil polynomials over F_p such that A has QM over F_p or F_p^2.
PQMpols:=function(p)
    return Setseq(Set(&cat[ Csqrt(f) : f in QMWeilPols(p,2) ]));
end function;


PQMF2:=PQMpols(2);
PQMF3:=PQMpols(3);
PQMF5:=PQMpols(5);

W4:=[ A : A in PQMF3 | Evaluate(A,1) eq 16 ];
assert #W16 eq 1;
W16:=W16[1];
Factorization(W16);
P16:=Evaluate(W16,1-z);
N:=NewtonPolygon(P16,2);
AllVertices(N);


Sort(Setseq(Set([ Evaluate(T,1) : T in PQMpols(p) ])));
