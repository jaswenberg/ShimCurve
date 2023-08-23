AttachSpec("spec");

N:=3;
B<i,j> := QuaternionAlgebra(Rationals(),-1,3);
Om := MaximalOrder(B);
iota:=FuchsianMatrixRepresentation(B);
Ogens:=Basis(Om);
BasisO:=Transpose(BasisMatrix(Om));
BasisOInverse:=BasisO^-1;
O_N:=QuaternionOrder([1] cat [N*x : x in Ogens]);
delta2 := 3*i+i*j; delta4 := 1+i; delta6 := 3+3*i+j+i*j;

coset_pool:=[ delta4^i*delta2^j : i in [0..3], j in [0,1] ];
coset_representatives:=[ coset_pool[1] ];
assert Norm(coset_representatives[1]) eq 1;

flag:=false;
GAMMA:="Gamma(N)";
while flag eq false do
coset_pool:=Setseq(Set([ beta*delta4^i*delta2^j : beta in coset_pool, i in [0..3], j in [0,1] ]));
  for x in coset_pool do
    if Norm(PrimitiveElement(Om,x)) eq 2 then
      //x;
      y:=PrimitiveElement(Om,x);
      //y; Norm(y);
      z:=PrimitiveElement(Om,x^2);
      z;
      coef:=Eltseq(z);
      assert ChangeUniverse(coef,GF(3))[1] eq GF(3)!0;
      assert ChangeUniverse(coef,GF(3)) ne ChangeUniverse([1,0,0,0],GF(3));
      print "/////////////";
      //flag:=true;
      //break;
    end if;
  end for;
end while;

coset_pool:=[ delta4^i*delta2^j : i in [0..3], j in [0,1] ];
coset_representatives:=[ coset_pool[1] ];
assert Norm(coset_representatives[1]) eq 1;
flag:=false;
while flag eq false do
coset_pool:=Setseq(Set([ beta*delta4^i*delta2^j : beta in coset_pool, i in [0..3], j in [0,1] ]));
  for x in coset_pool do
    if InGamma(Om,x^2,N,GAMMA) and Norm(PrimitiveElement(Om,x)) eq 3
      and InGamma(Om,(y*PrimitiveElement(Om,x))^2,N,GAMMA) then
      x;
      z:=PrimitiveElement(Om,x);
      z; Norm(z);
      flag:=true;
      break;
    end if;
  end for;
end while;

AL:=[1,y,z,y*z];
