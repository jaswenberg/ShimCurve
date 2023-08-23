//////////////////////////////////////////////

Rx<x>:=PolynomialRing(Rationals());
//this is phi : X^*(6,P2) -> X^*(6,1)
X := Curve(ProjectiveSpace(PolynomialRing(Rationals(), 2)));
KX<x> := FunctionField(X);

j:=(-64*x^20 + 256*x^16 - 384*x^12 + 256*x^8 - 64*x^4)/(x^24 + 42*x^20 + 591*x^16 + 2828*x^12 + 591*x^8 + 42*x^4 + 1);
j:=phi;
J2:=12*(j+1);
J4:=6*(j^2+j+1);
J6:=4*(j^3-2*j^2+1);
J8:=(J2*J6-J4^2)/4;
J10:=j^3;
BG6Igusa:=[J2,J4,J6,J8,J10];
C:=HyperellipticCurveFromIgusaInvariants(BG6Igusa);



















//////////////////////////////////////////////////////

/*monodromy:=[ Sym(24) | 
(1, 14)(2, 13)(3, 16)(4, 15)(5, 19)(6, 20)(7, 17)(8, 18)(9, 24)(10, 23)(11, 22)(12, 21),
(1, 24, 4, 23)(2, 22, 3, 21)(5, 14, 6, 16)(7, 15, 8, 13)(9, 19, 11, 18)(10, 17, 12, 20),
(1, 10, 6)(2, 12, 7)(3, 11, 5)(4, 9, 8)(13, 18, 22)(14, 19, 24)(15, 17, 23)(16, 20, 21) 
]; //the one JV found.

//GeneraTableToRecords(6,1,4: genus:=0, fuchsindex:=24, AutmuOnorms:={1,3}, torsioninvariants:=[2,2]);
ramification_data:=[ Sym(24) | 
(1, 2, 5)(3, 4, 10)(6, 7, 15)(8, 9, 16)(11, 12, 20)(13, 14, 21)(17, 18, 19)(22, 23, 24),
(1, 3, 8, 7)(2, 6, 13, 12)(4, 5, 11, 18)(9, 10, 17, 23)(14, 15, 16, 22)(19, 20, 21, 24),
(1, 4)(2, 7)(3, 9)(5, 12)(6, 14)(8, 15)(10, 18)(11, 19)(13, 20)(16, 23)(17, 24)(21, 22)
]; //the one the genera computations found.*/
B<i,j>:=QuaternionAlgebra<Rationals() | 3,-1 >;
O:=QuaternionOrder([ 1, 1/2 + 1/2*i + 1/2*j + 1/2*k, 1/2 - 1/2*i + 1/2*j - 1/2*k, 1/2 - 1/2*i - 1/2*j + 1/2*k ]);
[B!(O![1, 2, 2, 0]),
B!(O![3, 2, 0, 2]),
B!(O![3, 0, 0, 0]),
B!(O![3, 1, 0, 3]),
B!(O![3, 1, 1, 0])];
G:=sub< Sym(24) | monodromy >;

load "primitive-belyi-maps/code/primitivize.m";

X,phi:=BelyiMap(monodromy);
X;
phi;
//////////////////////////////
//this is (X,phi)













S<x>:=PolynomialRing(Rationals());
X:=EllipticCurve(S!x^3 + 27/242*x + 189/10648,S!0);
KX<x,y> := FunctionField(X);
phi:= (864/1331*x^9 + 34992/161051*x^7 + 61236/1771561*x^6 + 472392/19487171*x^5 + 1653372/214358881*x^4 + 59049/38974342*x^3 + 11160261/25937424601*x^2 + 78121827/1141246682444*x + 182284263/50214854027536)/(x^12 + 54/121*x^10 + 54/121*x^9 + 2187/29282*x^8 + 2187/14641*x^7 + 98415/1771561*x^6 + 59049/3543122*x^5 + 38795193/3429742096*x^4 + 610173/857435524*x^3 + 129140163/207499396808*x^2 + 531441/51874849202*x + 531441/51874849202);

A,map:=MordellWeilGroup(X); //Z/2 + Z
Q:=map(A.2);  //generator
//checking ramification indices to match up with Baba-Granath's j-line we must 
//do the linear fractional transformation 0-->oo which is LFT(phi,[3,2,1]) or LFT(phi,[3,1,2]);

perm:=[3,2,1];
BelyiMap:=LFT(phi,perm);
a_sqfree:=SquarefreeFactorization(-6*BelyiMap);
b_sqfree:=SquarefreeFactorization(-2*(27*BelyiMap+16));



for i in [1..10] do 
  q:=i*Q;i; q;

  aq:=a_sqfree(q);
  bq:=b_sqfree(q);

  a:=TrialRepresentativeModuloSquares(aq);
  b:=TrialRepresentativeModuloSquares(bq);
  H:=QuaternionAlgebra<Rationals() | a , b >;
  IsMatrixRing(H);
end for;


j:=BelyiMap(Q);
Rz<z>:=PolynomialRing(Rationals());
Kj<s>:=NumberField(z^2+6*j);
OKj:=Integers(Kj);
Kjv<v>:=PolynomialRing(Kj);
t:=-2*(27*j+16);
fj:=(-4+3*s)*v^6 + 6*t*v^5 + 3*t*(28+9*s)*v^4 - 4*t^2*v^3 + 3*t^2*(28-9*s)*v^2 + 6*t^3*v - t^3*(4+3*s);
Cj:=HyperellipticCurve(fj);
Jj:=Jacobian(Cj);

TorsionBound(Jj,100); //4
TorsionGroupHeuristicUpToTwist(Cj); //[2,2]
//load "QM-Mazur/fourtorsionfield.m";
//twotorspol, gens := fourtorsionfield(Cj);

denom_primes:=[ Denominator(a) : a in Coefficients(Cj) ];

MestreIsSplit:=false;
torsion:=true;
LinYang:=false;
D:=6;
exponent:=1;
bound:=50;
group:=AbelianGroup([2,4]);


//for perm in Permutations({1,2,3}) do //[3,1,2] from plugging in values looks like it has to be this one (its the only one with all 4-torsion defined over F_p^4.)
  perm:=[3,1,2];
  for i in [1..10] do 
    q:=i*Q;
    BelyiMap:=LFT(phi,perm);
    j:=BelyiMap(q);
    i;
    j;
    perm;
    MestreObstructionIsSplit(D,j : LinYang:=LinYang);
    /*if MestreIsSplit eq false or (MestreIsSplit eq true and MestreObstructionIsSplit(D,j : LinYang:=LinYang)) then  
      IgusaClebsch:=PQMIgusaClebsch(D,j : LinYang:=LinYang);
      //C:=HyperellipticCurveFromIgusaClebsch(IgusaClebsch);
      //if BaseRing(C) eq Rationals() then 
        if torsion eq true then
          tors_heur:=TorsionGroupHeuristicUpToTwist(IgusaClebsch : bound:=bound,exponent:=exponent, group:=group);
          if Type(tors_heur) eq MonStgElt then 
            tors_heur;
          else 
            invr_heur:=< PrimaryAbelianInvariants(gp) : gp in tors_heur >;
            inv:=Sprint(invr_heur);
            data:=Sprintf("%o||%o",IgusaClebsch, inv); 
            data;
          end if;
        end if; 
      //end if;
      end if;*/
  end for;
//end for;
  //GeneratePQMCurves(6 : BelyiMap:=psi, size:=10);
end for;


BelyiMapNum:=(803437664440576*z^12 + 358558957684224*z^10 - 162981344401920*z^9 + 60006767711616*z^8 - 54551607010560*z^7 + 16861405803264*z^6 - 6086336319360*z^5 + 2891009751696*z^4 - 645520518720*z^3 + 154330466400*z^2 - 46766808000*z + 5314410000);
BelyiMapDen:=(880099259770368*z^9 + 294578677857024*z^7 + 46864789659072*z^6 + 32866216124544*z^5 + 10457432403264*z^4 + 2054138507784*z^3 + 583369162992*z^2 + 92808730476*z + 4921675101);


//coef:=\frac{11^3}{2 \cdot 3^6}
//BelyiMapNum:=(x - 3/11)^4 \cdot (x^2 + 3/11x + 45/242)^4
//BelyiMapDen:=(x + 3/22)^3 \cdot (x^2 - 3/22x + 63/484)^3

/////////////////////////////
//compute some mestre obstructions for the linear fractional transformation which .

//[1,2,3],[1,3,2],[3,2,1],[3,1,2] mestre obstruction for first 6 points.





