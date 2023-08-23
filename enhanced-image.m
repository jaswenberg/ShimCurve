


intrinsic ElementToAutomorphismModN(a::AlgQuatElt, OmodN::AlgQuatOrdRes) -> GrpAutoElt
  {a in B^x becomes an automorphism of (O/N)^x by considering the map a |-> (x|-> a^-1xa) 
  as long as a \in N_B^x(O). We apply this to (O/N)^x as a permutation group.}

  O:=OmodN`quaternionorder;
  N:=OmodN`quaternionideal;
  ON,piN:=quo(O,N);
  ONx,phi,phi_inv:=UnitGroup(OmodN);
  aut:=hom< ONx -> ONx | x :-> phi_inv(piN(a^(-1)*(phi(x)`element)*a)) >;
  return AutomorphismGroup(ONx)!aut;
end intrinsic;

intrinsic ElementToAutomorphismModN(a::AlgQuatElt, O::AlgQuatOrd, N::RngIntElt) -> GrpAutoElt
  {a in B^x becomes an automorphism of (O/N)^x by considering the map a |-> (x|-> a^-1xa) 
  as long as a \in N_B^x(O). We apply this to (O/N)^x as a permutation group.}

  return ElementToAutomorphismModN(a,quo(O,N));
end intrinsic;


intrinsic AutomorphismsModN(S::{ AlgQuatProjElt }, OmodN::AlgQuatOrdRes) -> Map
  {Given a subset of Aut(O) input as a finite subset S of B^x, create the map
   theta : S -> Aut((O/N)^x)}
  
  ONx,phi:=UnitGroup(OmodN);
  return map< S -> AutomorphismGroup(ONx) | s:->ElementToAutomorphismModN(s,OmodN) >;
end intrinsic;

intrinsic AutomorphismsModN(S::{ AlgQuatProjElt }, O::AlgQuatOrd, N::RngIntElt) -> Map
  {Given a subset of Aut(O) input as a finite subset S of B^x, create the map
  theta : S -> Aut((O/N)^x)}
  
  OmodN:=quo(O,N);
  return AutomorphismsModN(S,OmodN);
end intrinsic;


intrinsic MapIsHomomorphism(AutmuO::. : injective:=true) -> BoolElt
  {Check whether the map AutmuO : C -> B^x/Q^x is an injective homomorphism}
  for x,y in Domain(AutmuO) do 
    if not(AutmuO(x*y) eq AutmuO(x)*AutmuO(y)) then 
      return false;
    end if;
    if injective eq true then 
      if ((AutmuO(x) eq AutmuO(y)) and (x ne y)) then 
        return false;
      end if;
    end if;
  end for;
  return true;
end intrinsic 




intrinsic NormalizingElementToGL4(x::AlgQuatElt,O::AlgQuatOrd: basis:=[]) -> GrpMatElt 
  {O is an order over R. For an element g \in N_Bx(O) the map phi_g : b |--> g^-1bg
  is R-linear hence [g] is an element of M_4(R) after fixing a basis
  this function computes [g] and also returns the R-basis of O.}

    //O:=OmodN`quaternionorder;
    //N:=OmodN`quaternionideal;
    //O:=MaximalOrder(Parent(x));
    if basis eq [] then 
      basis:=Basis(O);
    end if;
    R:=BaseRing(O);
    assert R eq Integers();
    M4R:=MatrixAlgebra(R,4);
    //ZmodN:=ResidueClassRing(N);

    x_map:=Transpose(M4R![ Eltseq(O!(x^(-1)*b*x)) : b in basis ]);
    assert Determinant(x_map) eq 1;

    return GL(4,R)!x_map, basis;
end intrinsic;


intrinsic NormalizingElementToGL4(x::AlgQuatProjElt,O::AlgQuatOrd : basis:=[]) -> GrpMatElt 
  {O is an order over R. For an element g \in N_Bx(O) the map phi_g : b |--> g^-1bg
  is R-linear hence [g] is an element of M_4(R) after fixing a basis
  this function computes [g] and also returns the R-basis of O.}

  return NormalizingElementToGL4(x`element, O : basis:=basis );
end intrinsic;


intrinsic NormalizingElementToGL4modN(x::AlgQuatElt,O::AlgQuatOrd, N::RngIntElt : basis:=[]) -> GrpMatElt 
  {O is an order over R. For an element g \in N_Bx(O) the map phi_g : b |--> g^-1bg
  is R-linear hence [g] is an element of M_4(R) after fixing a basis
  this function computes [g] and also returns the R-basis of O.}

  ZmodN:=ResidueClassRing(N);
  return GL(4,ZmodN)!NormalizingElementToGL4(x,O : basis:=basis);
end intrinsic;

intrinsic NormalizingElementToGL4modN(x::AlgQuatProjElt,O::AlgQuatOrd, N::RngIntElt : basis:=[]) -> GrpMatElt 
  {O is an order over R. For an element g \in N_Bx(O) the map phi_g : b |--> g^-1bg
  is R-linear hence [g] is an element of M_4(R) after fixing a basis
  this function computes [g] and also returns the R-basis of O.}

  ZmodN:=ResidueClassRing(N);
  return GL(4,ZmodN)!NormalizingElementToGL4(x`element,O : basis:=basis);
end intrinsic;
  



intrinsic UnitGroupToGL4(x::AlgQuatOrdElt : basis:=[]) -> GrpMatElt 
  {O is an order over R, this returns a matrix [lambda_g] wrt to a basis
  which is the right regular representation
  lambda_x : y --> y*x where g \in GL_1(O)}

  //OmodN:=Parent(x);
  //x0:=x`element;
  //O:=OmodN`quaternionorder;
  //N:=OmodN`quaternionideal;
  O:=Parent(x);
  if basis eq [] then 
    basis:=Basis(O);
  end if;
  R:=BaseRing(O);
  assert R eq Integers();
  M4R:=MatrixAlgebra(R,4);
  //ZmodN:=ResidueClassRing(N);

  x_map:=Transpose(M4R![ Eltseq(O!(b*x)) : b in basis ]);
  //assert ZmodN!Determinant(x_map) ne 0;
  return M4R!x_map;
end intrinsic;



intrinsic UnitGroupToGL4(x::AlgQuatOrdResElt : basis:=[]) -> GrpMatElt 
  {O is an order over R, this returns a matrix [lambda_g] wrt to a basis
  which is the right regular representation
  lambda_x : y --> y*x where g \in GL_1(O)}


  O:=Parent(x`element);
  if basis eq [] then 
    basis:=Basis(O);
  end if;

  return UnitGroupToGL4(x`element : basis:=basis);
end intrinsic;
 


intrinsic UnitGroupToGL4modN(x::AlgQuatOrdElt,N::RngIntElt : basis:=[]) -> GrpMatElt 
  {O is an order over R, this returns a matrix [lambda_g] wrt to a basis
  which is the right regular representation
  lambda_g : g --> b*g where g \in GL_1(O)}

  ZmodN:=ResidueClassRing(N);
  return GL(4,ZmodN)!UnitGroupToGL4(x);
end intrinsic;


intrinsic EnhancedSemidirectInGL4(Ocirc::AlgQuatEnh : basis:=[]) -> Map 
  {create the map from the semidirect product to GL4}

  O:=Ocirc`quaternionorder;
  R:=Ocirc`basering;
  if basis eq [] then 
    basis:=Basis(O);
  end if;
  GL4:=GL(4,R);
  if R eq Integers() then 
    mapfromenhancedimage := map<  Ocirc -> GL4  |  
    s :-> NormalizingElementToGL4((s`element)[1],O : basis:=basis)*UnitGroupToGL4((s`element)[2] : basis:=basis)  >;
  else 
    N:=Modulus(R);
    mapfromenhancedimage := map<  Ocirc -> GL4  |  
    s :-> NormalizingElementToGL4modN(s[1],O,N : basis:=basis)*UnitGroupToGL4modN(s[2],N : basis:=basis)  >;
  end if;

  return mapfromenhancedimage;
end intrinsic;
 

intrinsic EnhancedSemidirectInGL4modN(Ocirc::AlgQuatEnh,N::RngIntElt : basis:=[]) -> Map 
  {create the map from the semidirect product to GL4}

  O:=Ocirc`quaternionorder;
  //R:=O`basering;
  //GL4:=GL(4,R);
  //assert R eq Integers();
  if basis eq [] then 
    basis:=Basis(O);
  end if;

  ZmodN:=ResidueClassRing(N);
  GL4:=GL(4,ZmodN);
  mapfromenhancedimage := map<  Ocirc -> GL4  |  
    s :-> GL4!(NormalizingElementToGL4((s`element)[1],O : basis:=basis)*UnitGroupToGL4((s`element)[2] : basis:=basis))  >;
  
  return mapfromenhancedimage;
end intrinsic;



intrinsic EnhancedElementInGL4(g::AlgQuatEnhElt : basis:=[]) -> GrpMatElt
  {the enhanced element in GL4}

  Ocirc:=Parent(g);
  map:=EnhancedSemidirectInGL4(Ocirc : basis:=basis);
  return map(g);
end intrinsic;

intrinsic EnhancedElementInGL4modN(g::AlgQuatEnhElt,N::RngIntElt : basis:=[]) -> GrpMatElt
  {the enhanced element in GL4}

  Ocirc:=Parent(g);
  map:=EnhancedSemidirectInGL4modN(Ocirc,N : basis:=basis);
  return map(g);
end intrinsic;



  


intrinsic EnhancedImagePermutation(AutmuO::Map,OmodN::AlgQuatOrdRes) -> Grp 
  {AutmuO is a map from a finite group C -> B^x, which is isomorphic onto the image in B^x/Q^x. 
  We create the semidirect product of ONx by AutmuO, using AutomorphismModN as the map
  theta: AutmuO -> Aut(ONx)}

  assert MapIsHomomorphism(AutmuO : injective:=true);
  H:=Domain(AutmuO);
  ONx,phi := UnitGroup(OmodN);
  AutONx:=AutomorphismGroup(ONx);
  theta:=hom< H -> AutONx | h :-> ElementToAutomorphismModN(AutmuO(h),OmodN) >;

  rho_circ,m1,m2,m3:=SemidirectProduct(ONx,H,theta);
  return rho_circ,m1,m2,m3;
end intrinsic;

intrinsic EnhancedImagePermutation(AutmuO::.,O::AlgQuatOrd, N::RngIntElt) -> Grp 
  {AutmuO is a map from a finite group C -> B^x, which is isomorphic onto the image in B^x/Q^x. 
  We create the semidirect product of ONx by AutmuO, using AutomorphismModN as the map
  theta: AutmuO -> Aut(ONx)}

  OmodN:=quo(O,N);
  return EnhancedImagePermutation(AutmuO,OmodN);
end intrinsic;


intrinsic EnhancedElementRecord(elt::. : basis:=[]) -> Any
  {given <w,x> in Autmu(O) \rtimes (O/N) return <w,x> as a 
  record along with its embedding in GL_4xGL_4 and just GL_4}
  
  OmodN:=Parent(elt[2]);
  O:=OmodN`quaternionorder;
  N:=OmodN`quaternionideal;

  if basis ne [] then 
    basis:=Basis(O);
  end if;

  RF := recformat< n : Integers(),
  enhanced,
  GL4xGL4,
  GL4
  >
  ;  

  s := rec< RF | >;
  s`enhanced:=elt;
  s`GL4xGL4:=<NormalizingElementToGL4modN(elt[1]`element,O,N : basis:=basis), UnitGroupToGL4modN(elt[2]`element,N : basis:=basis)>;
  s`GL4:=s`GL4xGL4[1]*s`GL4xGL4[2];
  return s;
end intrinsic;


intrinsic EnhancedImageGL4(AutmuO::Map, OmodN::AlgQuatOrdRes) -> GrpMat
  {}

  O:=OmodN`quaternionorder;
  N:=OmodN`quaternionideal;
  basis:=Basis(O);
  assert MapIsHomomorphism(AutmuO : injective:=true);
  H:=Domain(AutmuO);
  ONx,phi:= UnitGroup(OmodN);
  UnitElements:=[ phi(x) : x in ONx ];
  ZmodN:=ResidueClassRing(N);
 
  auts:=[ AutmuO(a) : a in Domain(AutmuO) ];

  enhancedimage_cartesian:=[ c: c in CartesianProduct(auts, UnitElements) ];

  RF := recformat< n : Integers(),
  enhanced,
  GL4xGL4,
  GL4
  >
  ;

  enhancedimage:=[];
  for elt in enhancedimage_cartesian do 
    s := rec< RF | >;
    s`enhanced:=elt;
    s`GL4xGL4:=<NormalizingElementToGL4modN(elt[1],O,N: basis:=basis), UnitGroupToGL4modN(elt[2]`element,N : basis:=basis)>;
    s`GL4:=s`GL4xGL4[1]*s`GL4xGL4[2];
    Append(~enhancedimage,s);
  end for;

 /* semidirGL4xGL4seq:= [ <NormalizingElementToGL4modN(s[1],OmodN : basis:=basis),
     UnitGroupModNToGL4(s[2] : basis:=basis)> : s in enhancedimage ];
  semidirGL4seq:= [ a[1]*a[2] : a in semidirGL4xGL4seq ];
  semidirGL4:= sub< GL(4,ZmodN) |  semidirGL4seq >;
  assert #Set(semidirGL4) eq #semidirGL4xGL4seq;

  mapfromenhancedimage := map<  enhancedimage -> semidirGL4xGL4seq  |  
    s :-> <NormalizingElementToGL4modN(s[1],OmodN : basis:=basis), UnitGroupModNToGL4(s[2] : basis:=basis)>, 
    h :-> enhancedimage[Index(semidirGL4xGL4seq,h)]  >;
  maptogroup:= map< semidirGL4xGL4seq -> semidirGL4 |  a :-> a[1]*a[2], g :-> semidirGL4xGL4seq[Index(semidirGL4seq,g)]  >;
  EnhancedImageToGL4 := mapfromenhancedimage*maptogroup;
  */
  semidirGL4:= sub< GL(4,ZmodN) |  [ x`GL4 : x in enhancedimage ] >;

  return semidirGL4,enhancedimage;
end intrinsic;


intrinsic EnhancedImageGL4(AutmuO::Map, O::AlgQuatOrd, N::RngIntElt) -> GrpMat
  {}

  OmodN:=quo(O,N);
  return EnhancedImageGL4(AutmuO, OmodN);
end intrinsic;


intrinsic EnhancedImageGL4(O::AlgQuatOrd, mu::AlgQuatElt, N::RngIntElt) -> GrpMat
  {}

  AutmuO:=Aut(O,mu);
  assert MapIsHomomorphism(AutmuO);
  OmodN:=quo(O,N);
  return EnhancedImageGL4(AutmuO, OmodN);
end intrinsic;

intrinsic EnhancedImageGL4(O::AlgQuatOrd, mu::AlgQuatOrdElt, N::RngIntElt) -> GrpMat
  {}

  AutmuO:=Aut(O,mu);
  assert MapIsHomomorphism(AutmuO);
  OmodN:=quo(O,N);
  return EnhancedImageGL4(AutmuO, OmodN);
end intrinsic;



intrinsic AutmuOinGL4modN(AutmuO::Map,O::AlgQuatOrd,N::RngIntElt : basis:=[]) -> GrpMat 
  {}  
  if basis eq [] then 
    basis:=Basis(O);
  end if; 
  elts:=[ NormalizingElementToGL4modN(AutmuO(s),O,N : basis:=basis) : s in Domain(AutmuO) ];
  group:= sub< GL(4,ResidueClassRing(N)) | elts >;
  assert #group eq #elts;
  return group;
end intrinsic;


intrinsic AutmuOinGL4modN(O::AlgQuatOrd,mu::AlgQuatElt,N::RngIntElt : basis:=[]) -> GrpMat 
  {} 
  AutmuO:=Aut(O,mu);
  return AutmuOinGL4modN(AutmuO,O,N);
end intrinsic;

intrinsic AutmuOinGL4modN(O::AlgQuatOrd,mu::AlgQuatOrdElt,N::RngIntElt : basis:=[]) -> GrpMat 
  {} 
  AutmuO:=Aut(O,mu);
  return AutmuOinGL4modN(AutmuO,O,N);
end intrinsic;


intrinsic FixedSubspace(H::GrpMat) -> GrpAb 
  {}
  N:=#BaseRing(H);
  ZmodN:=ResidueClassRing(N);
  ZmodN4:= [ Matrix(ZmodN,1,4,[a,b,c,d]) : a,b,c,d in ZmodN ];
  fixed_vectors:= [ v : v in ZmodN4 | forall(u){ g : g in H | v*g eq v } ];
  A:=AbelianGroup([N,N,N,N]);
  elts:=[ Eltseq(v) : v in fixed_vectors ];
  fixedtors:=sub<A | elts >; 
  //fixedsub:=sub< AbelianGroup([N,N,N,N]) | 
  return fixedtors; //PrimaryAbelianInvariants(fixedsub);
end intrinsic;


intrinsic HasPolarizedElementOfDegree(O::AlgQuatOrd,d::RngIntElt) -> BoolElt, AlgQuatOrdElt 
  {return an element mu of O such that mu^2 + d*disc(O) = 0 if it exists.}
  disc:=Discriminant(O);
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
        return true, O!mu;
      else 
        assert zO^3 eq 1;
        tr,c:=IsSquare(Integers()!d*disc/3);
        mu:=(2*zO+1)*c;
        assert mu^2+d*disc eq 0;
        assert mu in O;
        return true,O!mu;
      end if;
    else 
      Rm:=Order([1,v]);
      mu,emb:=Embed(Rm,O);
      assert mu^2+d*disc eq 0;
      return true, O!mu;
    end if;
  else 
    return false;
  end if;
end intrinsic;


intrinsic DegreeOfPolarizedElement(O::AlgQuatOrd,mu:AlgQuatOrdElt) -> RngIntElt
  {degree of mu}
  tr,nmu:= IsScalar(mu^2);
  disc:=Discriminant(O);
  del:=-nmu/disc;
  assert IsCoercible(Integers(),del);
  assert IsSquarefree(Integers()!del);
  return Integers()!del;
end intrinsic;

intrinsic IsTwisting(O::AlgQuatOrd,mu::AlgQuatOrdElt) -> BoolElt
  {(O,mu) is twisting (of degree del = -mu^2/disc(O)) if there exists chi in O and N_Bx(O)
   such that chi^2 = m, m|Disc(O) and mu*chi = -chi*mu }

  tr,nmu:= IsScalar(mu^2);
  disc:=Discriminant(O);
  del:=DegreeOfPolarizedElement(O,mu);
  B:=QuaternionAlgebra(O);
  ram:=Divisors(disc);
  //ram:=//Divisors(disc); //cat [ -1*m : m in Divisors(disc) ];

  for m in ram do
  Bram<i1,j1>:=QuaternionAlgebra< Rationals() | -disc*del, m>;
  tr,isom:=IsIsomorphic(Bram, B : Isomorphism:=true);
    if tr eq true then

      chi:=isom(j1);
      if mu*chi eq -chi*mu and chi in O then
        twisted_basis:=[1,mu,chi,mu*chi];
        Omuchi:=QuaternionOrder(Integers(), twisted_basis);   
        assert IsIsomorphic(O,Omuchi);
        return true, m,twisted_basis;
      end if;
    end if;
  end for;
  return false;
end intrinsic;



intrinsic Aut(O::AlgQuatOrd,mu::AlgQuatOrdElt) -> Any
  {}

  assert IsScalar(mu^2);
  tr,eta:=IsScalar(mu^2);
  disc:=Discriminant(O);
  Rx<x>:=PolynomialRing(Rationals());
  Em<v>:=NumberField(x^2-eta);
  //Rm:=Order([1,v]);
  cyc,Czeta,zeta:=IsCyclotomic(Em);
  //Zzeta:=Integers(Czeta);

  B:=QuaternionAlgebra(O);
  BxmodQx:=QuaternionAlgebraModuloScalars(B);

  if cyc eq true then  
    sqeta,c:=SquarefreeFactorization(Integers()!eta);
    assert sqeta in {-1,-3};
    if sqeta eq -1 then 
      cyc_order:=4;
      zeta_n := mu/c;
    elif sqeta eq -3 then 
      cyc_order:=6;
      zeta_n := ((mu/c)+1)/2;
    end if;
    a:=B!zeta_n+1;
  else 
    cyc_order:=2;
    a:=B!mu;
  end if;

  if IsTwisting(O,mu) then
    tr,m,twisted_basis:=IsTwisting(O,mu);
    b:=B!(twisted_basis[3]);
    if cyc eq true then 
      Dn:=DihedralGroup(cyc_order);
    else 
      Dn:=Group("C2^2");
    end if;
    Dngens:=Generators(Dn);
    assert #Dngens eq 2;
    assert Order(Dn.1) eq #Dn/2;
    assert Order(Dn.2) eq 2;
    elts:= [ <Dn.1^l*Dn.2^k, BxmodQx!(a^l*b^k)> : l in [0..cyc_order-1], k in [0..1] ];
    grp_map:=map< Dn -> BxmodQx | elts >;
  else 
    if cyc eq true then 
      Cn:=CyclicGroup(cyc_order);
    else 
      Cn:=CyclicGroup(2);
    end if;
    elts:= [ <Cn.1^k,BxmodQx!(a^k)> : k in [0..#Cn-1] ];
    grp_map:=map< Cn -> BxmodQx | elts >;
  end if;
  
  assert MapIsHomomorphism(grp_map);
  return grp_map, [ grp_map(a) : a in Domain(grp_map) ];
end intrinsic;


intrinsic Aut(O::AlgQuatOrd,mu::AlgQuatElt) -> Any
  {}
  return Aut(O,O!mu);
end intrinsic;


intrinsic EnhancedCosetRepresentation(H::GrpMat, G::GrpMat,O::AlgQuatOrd,mu::AlgQuatOrdElt) -> Any 
  {Make the coset representation of H in G}
  N:=#BaseRing(H);

  NBOplusgens:=NormalizerPlusGeneratorsEnhanced(O,mu);
  NBOplusgensGL4:=[ EnhancedElementInGL4modN(g,N) : g in NBOplusgens ]; 

  assert -G!1 in G;
  Gplus:=sub< G | NBOplusgensGL4 >;
  assert #G/#Gplus eq 2;
  GO:= G meet sub< GL(4,ResidueClassRing(N)) | UnitGroup(O,N) >;

  K:=[ k : k in SemidirectToNormalizerKernel(O,mu) ];
  KG:=sub< Gplus | [ EnhancedElementInGL4modN(k,N) : k in K ] >;
 
  Gplusquo,Gmap:= quo< Gplus | KG >;

  Hplus := sub< Gplus | H meet Gplus >;
  HplusKG:= sub< Gplus | Hplus, KG >;
  HplusKGquoalt:= quo< HplusKG | KG >;

  Hplusquo:=Gmap(Hplus);

  T:=CosetTable(Gplusquo,Hplusquo);
  piH:=CosetTableToRepresentation(Gplusquo,T);

  return piH;
end intrinsic;


intrinsic EnhancedRamificationData(H::GrpMat, G::GrpMat,O::AlgQuatOrd,mu::AlgQuatOrdElt) -> Any
  {return the image of the elliptic elements under the monodromy map}

  N:=#BaseRing(H);
  assert -G!1 in G;
  NBOplusgens:=NormalizerPlusGeneratorsEnhanced(O,mu);
  NBOplusgensGL4:=[ EnhancedElementInGL4modN(g,N) : g in NBOplusgens ]; 
  Gplus:=sub< G | NBOplusgensGL4 >;
 
  elliptic_eltsGL4:= [ EnhancedElementInGL4modN(e,N) : e in EnhancedEllipticElements(O,mu) ]; 
  K:=[ k : k in SemidirectToNormalizerKernel(O,mu) ];
  KG:=sub< Gplus | [ EnhancedElementInGL4modN(k,N) : k in K ] >;

  Gplusquo,Gmap:= quo< Gplus | KG >;

  piH:=EnhancedCosetRepresentation(H,G,O,mu);
  sigma := [ piH(Gmap(v)) : v in elliptic_eltsGL4 ];

  return sigma;
end intrinsic;


intrinsic EnhancedGenus(H::GrpMat, G::GrpMat,O::AlgQuatOrd,mu::AlgQuatOrdElt) -> Any 
  {compute the genus}

  sigma:=EnhancedRamificationData(H,G,O,mu);
  return EnhancedGenus(sigma);
end intrinsic;


intrinsic AllEnhancedSubgroups(O::AlgQuatOrd,mu::AlgQuatOrdElt,N::RngIntElt : minimal:=false,PQMtorsion:=false,verbose:=true, lowgenus:=false, write:=false) -> Any
  {return all of the enhanced subgroups in a list with each one being a record}
  if write eq true then 
    assert verbose eq true;
    assert minimal eq false;
  end if;
  assert N gt 2;
  B:=QuaternionAlgebra(O);
  BxmodQx:=QuaternionAlgebraModuloScalars(B);
  OmodN:=quo(O,N);
  possible_tors:=[   [3], [2,3], [3,3], [4], [2,4], [2,2,2], [2,2,3],[3,4],[4,4], [2,2,4],[2,3,3] ];
  D:=Discriminant(B);
  del:=DegreeOfPolarizedElement(O,mu);

  //mu:=PolarizedElementOfDegree(O,1);
  AutFull:=Aut(O,mu);
  assert MapIsHomomorphism(AutFull : injective:=true);

  RF := recformat< n : Integers(),
    subgroup,
    genus,
    order,
    index,
    fixedsubspace,
    generators,
    split,
    endomorphism_representation,
    AutmuO_norms,
    ramification_data
    >
    ;

  NBOplusgens:=NormalizerPlusGeneratorsEnhanced(O,mu);
  NBOplusgensGL4:=[ EnhancedElementInGL4modN(g,N) : g in NBOplusgens ]; 

  G,Gelts:=EnhancedImageGL4(AutFull,O,N);
  assert -G!1 in G;
  Gplus:=sub< G | NBOplusgensGL4 >;
  assert #G/#Gplus eq 2;
  GO:= G meet sub< GL(4,ResidueClassRing(N)) | UnitGroup(O,N) >;
  //assert #G/4 eq #GO; //if twisting

  ZmodN:=ResidueClassRing(N);
  Autmuimage:=[AutFull(c) : c in Domain(AutFull) ];

  elliptic_eltsGL4:= [ EnhancedElementInGL4modN(e,N) : e in EnhancedEllipticElements(O,mu) ];
  K:=[ k : k in SemidirectToNormalizerKernel(O,mu) ];
  KG:=sub< Gplus | [ EnhancedElementInGL4modN(k,N) : k in K ] >;

  Gplusquo,Gmap:= quo< Gplus | KG >;

  minimal_subs_init:=<>;
  subs:=Subgroups(G);
  for H in subs do

    Hgp:=H`subgroup;
    fixedspace:=FixedSubspace(Hgp);

    gens:=Generators(Hgp);

    order:=H`order;
    //index:=Order(G)/order;

    Hplus := sub< Gplus | Hgp meet Gplus >;
    HplusKG:= sub< Gplus | Hplus, KG >;
    HplusKGquoalt:= quo< HplusKG | KG >;

    Hplusquo:=Gmap(Hplus);
    if not IsIsomorphic(Hplusquo,HplusKGquoalt) then 
      H;
    end if;

    index:=#Gplusquo/#Hplusquo;

    T:=CosetTable(Gplusquo,Hplusquo);
    piH:=CosetTableToRepresentation(Gplusquo,T);
    //piH := EnhancedCosetRepresentation(G,Hgp,Gammastar_plus);
    sigma := [ piH(Gmap(v)) : v in elliptic_eltsGL4 ];
    genus:=EnhancedGenus(sigma);

    Henh:=[ g`enhanced : g in Gelts | g`GL4 in Hgp ];
    Hautmus:= Setseq(Set([ h[1] : h in Henh ]));
    rho_end_norms:= Set([ Abs(SquarefreeFactorization(Integers()!Norm(w[1]`element))) : w in Henh ]);
    rho_end:= sub< GL(4,ZmodN) | [ NormalizingElementToGL4modN(w[1],O,N) : w in Henh ] >;
    // rho_end_size:=Integers()!#Hgp/(#(GO meet Hgp));

    is_split:=true;
    for w in Hautmus do 
      if <w,OmodN!(O!1)> notin Henh then 
        is_split := false;
      end if;
    end for;

    HGL4gens:=Generators(Hgp);
    Henhgens:=< g`enhanced : g in Gelts | g`GL4 in HGL4gens >;

    s := rec< RF | >;
    s`subgroup:=Hgp;
    s`genus:=genus;
    s`order:=order;
    s`index:=index;
    s`fixedsubspace:=PrimaryAbelianInvariants(fixedspace);
    s`endomorphism_representation:=GroupName(rho_end);
    s`AutmuO_norms:=rho_end_norms;
    s`split:=is_split;
    s`generators:=Henhgens;
    s`ramification_data:=sigma;

    if PQMtorsion eq true then 
      if s`endomorphism_representation ne "C1" and s`fixedsubspace in possible_tors then
        if lowgenus eq true then  
          if genus le 1 then 
            Append(~minimal_subs_init,s);
          end if;
        else 
          Append(~minimal_subs_init,s);
        end if;
      end if;
    else 
      if lowgenus eq true then  
        if genus le 1 then 
          Append(~minimal_subs_init,s);
        end if;
      else 
        Append(~minimal_subs_init,s);
      end if;
    end if;
  end for;

  if minimal eq false then 
    if verbose eq true then 
      printf "Quaternion algebra of discriminant %o with presentation\n",Discriminant(O);
      print B : Magma;
      printf "Basis of O is %o\n", Basis(O);
      printf "Level N = %o\n", N;
      printf "Polarized Element \\mu=%o of degree %o and norm %o\n", mu, DegreeOfPolarizedElement(O,mu),Norm(mu);
      print "Genus ? (Fuchsian) Index ? #H ? Torsion ? Gal(L|Q) ? AutmuO norms ? Split semidirect ? Generators ? Ramification Data \n";
      for s in minimal_subs_init do 
        printf "%o ? %o ? %o ? %o ? %o ? %o ? %o ? %o \n", s`genus, s`index, s`order, s`fixedsubspace, s`endomorphism_representation, s`AutmuO_norms, s`split, s`generators, Sprint(s`ramification_data : oneline:=true);
      end for;
      if write eq true then 
        filename:=Sprintf("QM-Mazur/genera-tables/genera-D%o-deg%o-N%o.m",D,del,N);
        Write(filename,Sprintf("%m;",B));
        Write(filename,Sprintf("%o;",Basis(O)));
        Write(filename,Sprintf("%o;",N));
        Write(filename,Sprintf("%o;",Eltseq(O!mu)));
        //Write(filename,Sprintf("Discriminant %o",Discriminant(O)));
        //Write(filename,Sprintf("Basis of O is %o", Basis(O)));
        //Write(filename,Sprintf("Level N = %o", N));
        Write(filename,Sprintf("Polarized Element \\mu=%o of degree %o and norm %o", mu, DegreeOfPolarizedElement(O,mu),Norm(mu)));
        Write(filename,"Genus ? (Fuchsian) Index ? #H ? Torsion ? Gal(L|Q) ? AutmuO norms ? Split semidirect ? Generators ? Ramification Data");

        for s in minimal_subs_init do 
          gens_readable:=[ Sprintf("< %o, %o >", g[1], Eltseq(g[2]`element)) : g in s`generators ];
          gens_readable;
          Write(filename,Sprintf("%o ? %o ? %o ? %o ? %o ? %o ? %o ? %o ? %o", s`genus, s`index, s`order, s`fixedsubspace, s`endomorphism_representation, s`AutmuO_norms, s`split, gens_readable, Sprint(s`ramification_data : oneline:=true)));
        end for;
      end if;
    end if;
    return minimal_subs_init;
  else 
    minimal_subs:=<>;
    for s in minimal_subs_init do  
      F:=s`subgroup;
      tors:=s`fixedsubspace;
      //endorep:=s`endomorphism_representation;
      //AL:=s`atkin_lehners;
      if exists(e){ N : N in minimal_subs_init | F subset N`subgroup and 
        tors eq N`fixedsubspace and F ne N`subgroup }
        //or exists(e){ N : N in minimal_subs_init | IsGLConjugate(F,N`subgroup) } 
        then 
        ;
      else 
        Append(~minimal_subs,s);
      end if;
    end for;
    if verbose eq true then
      printf "Quaternion algebra of discriminant %o with presentation\n",Discriminant(O);
      print B : Magma;
      printf "Basis of O is %o\n", Basis(O);
      printf "Level N = %o\n", N;
      printf "Polarized Element \\mu=%o of degree %o and norm %o\n", mu, DegreeOfPolarizedElement(O,mu),Norm(mu);
      print "Genus ? (Fuchsian) Index ? #H ? Torsion ? Gal(L|Q) ? AutmuO norms ? Split semidirect ? Generators ? Ramification Data\n";
      for s in minimal_subs do 
        printf "%o ? %o ? %o ? %o ? %o ? %o ? %o ? %o \n", s`genus, s`index, s`order, s`fixedsubspace, s`endomorphism_representation, s`AutmuO_norms, s`split, Sprint(s`generators), Sprint(s`ramification_data : oneline:=true);
      end for;
    end if;
    return minimal_subs;
  end if;

end intrinsic;


intrinsic AllEnhancedSubgroups(B::AlgQuat,mu::AlgQuatOrdElt,N::RngIntElt : minimal:=false,PQMtorsion:=false,verbose:=true, lowgenus:=false, write:=false) -> Any
  {}
  return AllEnhancedSubgroups(MaximalOrder(B),mu,N : minimal:=minimal, verbose:=verbose, PQMtorsion:=PQMtorsion, lowgenus:=lowgenus, write:=write);
end intrinsic;

intrinsic AllEnhancedSubgroups(O::AlgQuatOrd,del::RngIntElt,N::RngIntElt : minimal:=false,PQMtorsion:=false,verbose:=true, lowgenus:=false, write:=false) -> Any
  {}
  if HasPolarizedElementOfDegree(O,del) then 
    tr,mu:=HasPolarizedElementOfDegree(O,del);
    return AllEnhancedSubgroups(O,mu,N : minimal:=minimal, verbose:=verbose, PQMtorsion:=PQMtorsion, lowgenus:=lowgenus, write:=write);
  else 
    printf "No polarization of degree %o\n", del;
    return "";
  end if;
end intrinsic;

intrinsic AllEnhancedSubgroups(B::AlgQuat,del::RngIntElt,N::RngIntElt : minimal:=false,PQMtorsion:=false,verbose:=true, lowgenus:=false, write:=false) -> Any
  {}
  O:=MaximalOrder(B);
  return AllEnhancedSubgroups(O,del,N : minimal:=minimal, verbose:=verbose, PQMtorsion:=PQMtorsion, lowgenus:=lowgenus, write:=write);
end intrinsic;

intrinsic AllEnhancedSubgroups(D::RngIntElt,del::RngIntElt,N::RngIntElt : minimal:=false,PQMtorsion:=false,verbose:=true, lowgenus:=false, write:=false) -> Any
  {}
  B:=QuaternionAlgebra(D);
  O:=MaximalOrder(B);
  return AllEnhancedSubgroups(O,del,N : minimal:=minimal, verbose:=verbose, PQMtorsion:=PQMtorsion, lowgenus:=lowgenus, write:=write);
end intrinsic;




intrinsic Print(elt::AlgQuatOrdResElt)
{.}
  printf "%o", elt`element;
end intrinsic;

intrinsic Print(OmodN::AlgQuatOrdRes)
{.}
  printf "Quotient of %o by %o", OmodN`quaternionorder, OmodN`quaternionideal;
end intrinsic;

intrinsic Print(elt::AlgQuatProjElt)
{.}
  printf "%o", elt`element;
end intrinsic;

intrinsic Print(BxmodFx::AlgQuatProj)
{.}
  printf "Quotient by scalars of %o", BxmodFx`quaternionalgebra;
end intrinsic;





