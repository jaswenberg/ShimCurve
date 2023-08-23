//////////////////////////////
//SetVerbose("Shimura", 3);
//DegreeBound := 1 and prec := (40 or so)
//work in BelyiDB-master

/*
B<i,j> := QuaternionAlgebra(Rationals(),-1,3);
Om := MaximalOrder(B);
iota:=FuchsianMatrixRepresentation(B);
Ogens:=Basis(Om);
BasisO:=Transpose(BasisMatrix(Om));
BasisOInverse:=BasisO^-1;
O_N:=QuaternionOrder([1] cat [N*x : x in Ogens]); //doesn't work
delta2 := 3*i+i*j; delta4 := 1+i; delta6 := 3+3*i+j+i*j;

//Normalizers
//w2:=1+i; w6:=3*i+i*j; w3:=w2^-1*w6;

//Change of basis matrix from <i,j> presentation to Ogens;


/*intrinsic OgensCoefficients(x::AlgQuatElt) -> ModMatFldElt
    {return the coordinates of writing the element x in terms of the basis Ogens}
    return Matrix(BasisOInverse)*Matrix(Rationals(), 4,1, ElementToSequence(x));
end intrinsic;

intrinsic OgensCoefficientsScaled(x::AlgQuatElt) -> ModMatFldElt
   {scale the previous function so that the coordinates are integers.}
   vec:=OgensCoefficients(x);
   scaled:=(Integers()!LCM([ Denominator(vec[m,1]) : m in [1..4] ])/GCD([ Numerator(vec[m,1]) : m in [1..4] ]))*vec;
   return  scaled;
end intrinsic;

intrinsic ElementScaled(x::AlgQuatElt) -> AlgQuatElt
       {return the element which is gotten by scaling x to have integral coefficients as in the previous function}
       return  &+[ OgensCoefficientsScaled(x)[m,1]*Ogens[m] : m in [1..4] ];
end intrinsic;*/
///////////////////

intrinsic PrimitiveElement(Om::AlgQuatOrd,x::AlgQuatElt) -> AlgQuatElt
  {We consider the coset of x in B>0^x/Q^x: this coset has a unique representative
  b of squarefree and integral norm. Return b.}

  num:=Integers()!Numerator(Norm(x));
  den:=Integers()!Denominator(Norm(x));
  _,squarepart_num:=SquarefreeFactorization(num);
  sqfree_den,squarepart_den:=SquarefreeFactorization(den);
  b:=x*(sqfree_den*squarepart_den/squarepart_num);
  assert IsSquarefree(Integers()!Norm(b));
  return Algebra(Om)!b;
end intrinsic;


intrinsic InGamma(Om::AlgQuatOrd,y::AlgQuatElt,N::RngIntElt,GAMMA::MonStgElt : SqrtP:=false) -> BoolElt
  {see if y\in B^x/Q^x is in Q^xGAMMA/Q^x}

  if GAMMA ne "Gamma(N)" then assert GCD(N,Discriminant(Om)) eq 1; end if;
  b:=PrimitiveElement(Om,y);
  if Norm(b) eq 1 then
    //this checks b in Om^1
    assert b in Om and b^(-1) in Om;
    if N eq 1 then
      assert b in Om or -b in Om;
      return true;
    end if;
    if GCD(N,Discriminant(Om)) eq 1 then
      BO:=Algebra(Om);
      Bp,iotap:=pMatrixRing(BO,N);
      Qp:=pAdicField(N); Fp:=pAdicQuotientRing(N,1);
      elt_id:=[ Fp!a : a in Eltseq(iotap(1)) ];
      if GAMMA eq "Gamma0(N)" then
      //upper triangular mod N
        if (Fp!(iotap(b)[2,1]) eq Fp!0) or (Fp!(iotap(-b)[2,1]) eq Fp!0) then
            return true;
        else
            return false;
        end if;
      elif GAMMA eq "Gamma1(N)" then
      //1, * on diagonal mod N
        if ((Fp!iotap(b)[1,1] eq Fp!1) or (Fp!iotap(-b)[1,1] eq Fp!1)) and
          ((Fp!iotap(b)[2,2] eq Fp!1) or (Fp!iotap(-b)[2,2] eq Fp!1)) and
          ((Fp!iotap(b)[2,1] eq Fp!0) or (Fp!iotap(-b)[2,1] eq Fp!0)) then
          return true;
        else
          return false;
        end if;
      elif GAMMA eq "Gamma(N)" then
        //identity mod N
        if ([ Fp!a : a in Eltseq(iotap(b)) ] eq elt_id) or ([ Fp!a : a in Eltseq(iotap(-b)) ] eq elt_id) then
            return true;
        else
            return false;
        end if;
      end if;
    else
      assert GAMMA eq "Gamma(N)";
      if SqrtP eq false then
        exp:=1;
      else
        exp:=2;
      end if;

      if N eq 2 then
        if ((b-1)^exp in N*Om) or ((-b-1)^exp in N*Om) then
          return true;
        else
          return false;
        end if;
      else
        if ((b-1)^exp in N*Om) then
          return true;
        else
          return false;
        end if;
      end if;
    end if;
  else
    return false;
  end if;
end intrinsic;


intrinsic SameProjectiveCoset(Om::AlgQuatOrd,alpha::AlgQuatElt,beta::AlgQuatElt,N::RngIntElt,GAMMA::MonStgElt,atkin_lehner::SeqEnum : SqrtP:=false) -> BoolElt
  {Given a subgroup Q^xGamma/Q^x of N_B>0^x/Q^x determined
  by the level N and the string Gamma  decide whether alpha
  and beta represent the same coset up to
  some specified Atkin-Lehner representatives}

  for delta in atkin_lehner do   //change to be right cosets!?
    gamma:=(delta^-1)*(beta^-1)*(alpha);
    if InGamma(Om,gamma,N,GAMMA : SqrtP:=SqrtP) then
        return true;
    end if;
  end for;
  return false;
end intrinsic;


///////////////////
intrinsic CosetRepresentatives(Om::AlgQuatOrd,N::RngIntElt,GAMMA::MonStgElt : SqrtP:=false) -> SeqEnum
  {return a list of primitive coset
  representatives for (N_B(O)/QQ^x)/(QQ^xGamma/QQ^x)}
  BO<i,j>:=Algebra(Om);
  assert i^2 eq -1;
  assert j^2 eq 3;
  delta2 := BO!(3*i+i*j); delta4 := BO!(1+i); delta6 := BO!(3+3*i+j+i*j);

  assert GAMMA eq "Gamma(N)";
  if GAMMA eq "Gamma0(N)" then
      index:=4*(N+1);
      assert GCD(N,6) eq 1;
  elif GAMMA eq "Gamma1(N)" then
      index:=4*(N+1)*(N-1)/2;
      assert GCD(N,6) eq 1;
  elif GAMMA eq "Gamma(N)" then
    if N eq 2 then
      if SqrtP eq false then
        index:=4*(N^4-N^2);
      else
        index:=4*(N^2-1);
      end if;
    else
      index:=144;
      //index:=4*(N^2*(N+1))/2;
    end if;
  end if;

  coset_pool:=[ delta4^i*delta2^j : i in [0..3], j in [0,1] ];
  coset_representatives:=[ coset_pool[1] ];
  assert Norm(coset_representatives[1]) eq 1;

  while #coset_representatives lt index do
  coset_pool:=Setseq(Set([ beta*delta4^i*delta2^j : beta in coset_pool, i in [0..3], j in [0,1] ]));
    for beta in coset_pool do
      u:=PrimitiveElement(Om,beta);
      alphas:= [ alpha : alpha in coset_representatives | SameProjectiveCoset(Om,alpha,u,N,GAMMA,[1] : SqrtP:=SqrtP) ];
      assert #alphas le 1;
      if #alphas eq 0 then
        Append(~coset_representatives, u);
      end if;
    end for;
  end while;

  return coset_representatives;
end intrinsic;

intrinsic AtkinLehnerRepresentatives(Om::AlgQuatOrd,N::RngIntElt,GAMMA::MonStgElt,W::SeqEnum : SqrtP:=false) -> SeqEnum
  {compute Atkin-Lehner representatives for W \subseteq [1,2,3,6]}
/*  BO:=Algebra(Om);
  if W eq [1] then
    return [BO!1];
  end if;
  coset_reps:=CosetRepresentatives(Om,N,GAMMA : SqrtP:=SqrtP);

  nm1:=[ x : x in coset_reps | Norm(x) eq 1 ];
  nm2:=[ x : x in coset_reps | Norm(x) eq 2 ];
  nm3:=[ x : x in coset_reps | Norm(x) eq 3 ];
  nm6:=[ x : x in coset_reps | Norm(x) eq 6 ];
  assert (#nm1 eq #coset_reps/4) and (#nm2 eq #coset_reps/4) and
  (#nm3 eq #coset_reps/4) and (#nm6 eq #coset_reps/4);

  ALcosets:=[ [a1,x,y,x*y] : a1 in nm1, x in nm2, y in nm3 |
  InGamma(Om,a1^2,N,GAMMA) and InGamma(Om,x^2,N,GAMMA) and
  InGamma(Om,y^2,N,GAMMA) and InGamma(Om,(x*y)^2,N,GAMMA) ];
  //[ x : x in nm2 | InGamma(Om,x^2,N,GAMMA) ];

  ALRs:=[ list : list in ALcosets |  SameProjectiveCoset(Om,BO!1,list[2],N,GAMMA,list : SqrtP:=SqrtP) and
  SameProjectiveCoset(Om,BO!1,list[3],N,GAMMA,list : SqrtP:=SqrtP) and SameProjectiveCoset(Om,BO!1,list[4],N,GAMMA,list : SqrtP:=SqrtP) ];
  assert ALRs eq ALcosets;
  assert ALRs ne [];
  if 6 in W then
    Exclude(~W,6);
    Append(~W,4);
  end if;
  return [ ALRs[1][m] : m in W ];*/
  BO<i,j>:=Algebra(Om);
  assert i^2 eq -1;
  assert j^2 eq 3;
  delta2 := 3*i+i*j; delta4 := 1+i; delta6 := 3+3*i+j+i*j;

  coset_pool:=[ delta4^i*delta2^j : i in [0..3], j in [0,1] ];
  coset_representatives:=[ coset_pool[1] ];
  assert Norm(coset_representatives[1]) eq 1;
  flag:=false;
  while flag eq false do
  coset_pool:=Setseq(Set([ beta*delta4^i*delta2^j : beta in coset_pool, i in [0..3], j in [0,1] ]));
    for x in coset_pool do
      if InGamma(Om,x^2,N,GAMMA :SqrtP:=SqrtP) and Norm(PrimitiveElement(Om,x)) eq 2 then
        y:=PrimitiveElement(Om,x);
        flag:=true;
        break;
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
      if InGamma(Om,x^2,N,GAMMA : SqrtP:=SqrtP) and Norm(PrimitiveElement(Om,x)) eq 3
        and InGamma(Om,(y*PrimitiveElement(Om,x))^2,N,GAMMA : SqrtP:=SqrtP) then
        z:=PrimitiveElement(Om,x);
        flag:=true;
        break;
      end if;
    end for;
  end while;

  AL:=[1,y,z,y*z];
  return AL;
end intrinsic;



intrinsic ActionToPermutation(Om::AlgQuatOrd,g::AlgQuatElt, N::RngIntElt,GAMMA::MonStgElt,W::SeqEnum : SqrtP:=false) -> GrpPermElt
  {make the coset rep N_B(O) ---> S_n with the cosets representatives of the relevent Fuchsian group}

  coset_reps:=CosetRepresentatives(Om,N,GAMMA : SqrtP:=SqrtP);
  nm1:=[ x : x in coset_reps | Norm(x) eq 1 ];
  nm2:=[ x : x in coset_reps | Norm(x) eq 2 ];
  nm3:=[ x : x in coset_reps | Norm(x) eq 3 ];
  nm6:=[ x : x in coset_reps | Norm(x) eq 6 ];
  nms:=&cat[nm1,nm2,nm3,nm6];

  cosets:=nms;
  atkin_lehner:=AtkinLehnerRepresentatives(Om,N,GAMMA,W : SqrtP:=SqrtP);
  permutation_indices:=[];
  for i in [1..#cosets] do
      betas:=[ beta : beta in cosets | SameProjectiveCoset(Om,beta, g*cosets[i], N,GAMMA,atkin_lehner : SqrtP:=SqrtP) ];
      assert #betas eq 1;
      Append(~permutation_indices,Index(cosets, betas[1]));
  end for;

  return Sym(#cosets)!permutation_indices;
end intrinsic;


intrinsic QuaternionTriple(Om::AlgQuatOrd,N::RngIntElt,GAMMA::MonStgElt,W::SeqEnum : SqrtP:=false) -> Any
    {generate the permutation triple given by the image of the coset rep on the generators}

    BO<i,j>:=Algebra(Om);
    assert i^2 eq -1;
    assert j^2 eq 3;
    delta2 := BO!(3*i+i*j); delta4 := BO!(1+i); delta6 := BO!(3+3*i+j+i*j);

    s2:=ActionToPermutation(Om,delta2,N,GAMMA,W : SqrtP:=SqrtP);
    s4:=ActionToPermutation(Om,delta4,N,GAMMA,W : SqrtP:=SqrtP);
    s6:=ActionToPermutation(Om,delta6,N,GAMMA,W : SqrtP:=SqrtP);
    PR:=[s2,s4,s6];
    G:=sub< Parent(s2) | s2,s4,s6 >;
    assert IsTransitive(G);
    assert s6*s4*s2 eq Identity(G);
    return PR, G;

end intrinsic;




 QuotientTriple := function(Z,G,perm_triple)
    assert Z subset Centralizer(Sym(Degree(G)), G);
    GZblock:=Set([ Orbit(Z,{i}) : i in [1..Degree(G)] ]);
    GZpart:={ Set([ Random(a) : a in Setseq(Set(x)) ]) : x in GZblock };
    psi:=BlocksAction(G,GZpart);
    PRmodZ:=[ psi(h) : h in perm_triple ];
    return PRmodZ, BlocksImage(G,GZpart);
end function;


QuaternionTripleGenus:=function(perm_triple)
    return (Degree(Parent(perm_triple[1]))+2 - #CycleDecomposition(perm_triple[1]) - #CycleDecomposition(perm_triple[2]) - #CycleDecomposition(perm_triple[3]))/2;
end function;
