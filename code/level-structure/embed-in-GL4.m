

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





intrinsic NormalizingElementToGL4(w::AlgQuatElt,O::AlgQuatOrd: basis:=[]) -> GrpMatElt 
  {O is an order over R. For an element g \in N_Bx(O) the map phi_g : b |--> g^-1bg
  is R-linear hence [g] is an element of M_4(R) after fixing a basis
  this function computes [g] and also returns the R-basis of O.}

  if basis eq [] then 
    basis:=Basis(O);
  end if;
  R:=BaseRing(O);
  assert R eq Integers();
  M4R:=MatrixAlgebra(R,4);

  w_map:=M4R![ Eltseq(O!(w^(-1)*b*w)) : b in basis ];
  assert Determinant(w_map) eq 1;

  return GL(4,R)!w_map, basis;
end intrinsic;


intrinsic NormalizingElementToGL4(w::AlgQuatProjElt,O::AlgQuatOrd : basis:=[]) -> GrpMatElt 
  {O is an order over R. For an element g \in N_Bx(O) the map phi_g : b |--> g^-1bg
  is R-linear hence [g] is an element of M_4(R) after fixing a basis
  this function computes [g] and also returns the R-basis of O.}

  return NormalizingElementToGL4(w`element, O : basis:=basis );
end intrinsic;


intrinsic NormalizingElementToGL4modN(w::AlgQuatElt,O::AlgQuatOrd, N::RngIntElt : basis:=[]) -> GrpMatElt 
  {O is an order over R. For an element g \in N_Bx(O) the map phi_g : b |--> g^-1bg
  is R-linear hence [g] is an element of M_4(R) after fixing a basis
  this function computes [g] and also returns the R-basis of O.}

  ZmodN:=ResidueClassRing(N);
  return GL(4,ZmodN)!NormalizingElementToGL4(w,O : basis:=basis);
end intrinsic;

intrinsic NormalizingElementToGL4modN(w::AlgQuatProjElt,O::AlgQuatOrd, N::RngIntElt : basis:=[]) -> GrpMatElt 
  {O is an order over R. For an element g \in N_Bx(O) the map phi_g : b |--> g^-1bg
  is R-linear hence [g] is an element of M_4(R) after fixing a basis
  this function computes [g] and also returns the R-basis of O.}

  ZmodN:=ResidueClassRing(N);
  return GL(4,ZmodN)!NormalizingElementToGL4(w`element,O : basis:=basis);
end intrinsic;
  


intrinsic UnitGroupToGL4(x::AlgQuatOrdElt : basis:=[]) -> GrpMatElt 
  {O is an order over R, this returns a matrix [lambda_g] wrt to a basis
  which is the right regular representation
  lambda_x : y --> y*x where g \in GL_1(O)}

  O:=Parent(x);
  if basis eq [] then 
    basis:=Basis(O);
  end if;
  R:=BaseRing(O);
  assert R eq Integers();
  M4R:=MatrixAlgebra(R,4);
  //ZmodN:=ResidueClassRing(N);

  x_map:=M4R![ Eltseq(O!(b*x)) : b in basis ];
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

intrinsic UnitGroupToGL4modN(x::AlgQuatOrdResElt,N::RngIntElt : basis:=[]) -> GrpMatElt 
  {O is an order over R, this returns a matrix [lambda_g] wrt to a basis
  which is the right regular representation
  lambda_g : g --> b*g where g \in GL_1(O)}

  return UnitGroupToGL4modN(x`element,N : basis:=basis);
end intrinsic;



intrinsic EnhancedSemidirectInGL4(Ocirc::AlgQuatEnh : basis:=[]) -> Map 
  {create the map from the semidirect product to GL4(R). R depends on the base 
  ring of Ocirc.}

  O:=Ocirc`quaternionorder;
  R:=Ocirc`basering;
  if basis eq [] then 
    basis:=Basis(O);
  end if;
  GL4:=GL(4,R);
  if Type(R) eq RngInt then 
    mapfromenhancedimage := map<  Ocirc -> GL4  |  
    s :-> NormalizingElementToGL4((s`element)[1],O : basis:=basis)*UnitGroupToGL4((s`element)[2] : basis:=basis)  >;
  else 
    N:=Modulus(R);
    mapfromenhancedimage := map<  Ocirc -> GL4  |  
    s :-> NormalizingElementToGL4modN((s`element)[1],O,N : basis:=basis)*UnitGroupToGL4modN(((s`element)[2])`element,N: basis:=basis)  >;
  end if;

  return mapfromenhancedimage;
end intrinsic;


intrinsic EnhancedSemidirectInGL4(O::AlgQuatOrd : basis:=[]) -> Map 
  {create the map from the semidirect product to GL4(R). R depends on the base 
  ring of Ocirc}

  Ocirc:=EnhancedSemidirectProduct(O);
  return EnhancedSemidirectInGL4(Ocirc);
end intrinsic;



intrinsic EnhancedSemidirectInGL4modN(Ocirc::AlgQuatEnh,N::RngIntElt : basis:=[]) -> Map 
  {create the map from the semidirect product to GL4(Z/NZ)}

  O:=Ocirc`quaternionorder;

  if basis eq [] then 
    basis:=Basis(O);
  end if;

  ZmodN:=ResidueClassRing(N);
  GL4:=GL(4,ZmodN);
  mapfromenhancedimage := map<  Ocirc -> GL4  |  
    s :-> GL4!(NormalizingElementToGL4((s`element)[1],O : basis:=basis)*UnitGroupToGL4((s`element)[2] : basis:=basis))  >;
  
  return mapfromenhancedimage;
end intrinsic;


intrinsic EnhancedSemidirectInGL4modN(O::AlgQuatOrd,N::RngIntElt : basis:=[]) -> Map 
  {create the map from the semidirect product to GL4(Z/NZ)}

  Ocirc:=EnhancedSemidirectProduct(O : N:=N);
  return EnhancedSemidirectInGL4modN(Ocirc,N);
end intrinsic;




intrinsic EnhancedElementInGL4(g::AlgQuatEnhElt : basis:=[]) -> GrpMatElt
  {the enhanced element in GL4(R), R depends on the base ring of g}

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






intrinsic EnhancedElementRecord(elt::AlgQuatEnhElt : basis:=[]) -> Any
  {given <w,x> in Autmu(O) \rtimes (O/N)^x or Autmu(O) \rtimes O^x  return <w,x> as a 
  record along with its embedding in GL_4xGL_4 and just GL_4}
  
  Ocirc:=Parent(elt);
  O:=Ocirc`quaternionorder;
  R:=Ocirc`basering;
  if Type(R) eq RngInt then 
    N:=0;
  else 
    N:=Modulus(R);
  end if;

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
  if N eq 0 then 
    s`GL4xGL4:=<NormalizingElementToGL4(elt`element[1],O: basis:=basis), UnitGroupToGL4(elt`element[2] : basis:=basis)>;
  else 
    s`GL4xGL4:=<NormalizingElementToGL4modN(elt`element[1],O,N : basis:=basis), UnitGroupToGL4modN(elt`element[2],N : basis:=basis)>;
  end if;
  s`GL4:=s`GL4xGL4[1]*s`GL4xGL4[2];
  return s;
end intrinsic;


intrinsic EnhancedImageGL4(AutmuO::Map, OmodN::AlgQuatOrdRes) -> GrpMat
  {return the image of the enhanced semidirect product group G in GL4(Z/NZ). The second return value 
  is a list of enhanced elements in record format.}

  O:=OmodN`quaternionorder;
  N:=OmodN`quaternionideal;
  Ocirc:=EnhancedSemidirectProduct(O: N:=N);
  basis:=Basis(O);
  assert MapIsHomomorphism(AutmuO : injective:=true);
  H:=Domain(AutmuO);
  ONx,phi:= UnitGroup(OmodN);
  UnitElements:=[ phi(x) : x in ONx ];
  ZmodN:=ResidueClassRing(N);
 
  auts:=[ AutmuO(a) : a in Domain(AutmuO) ];

  enhanced_elements:=[ Ocirc!<w,x> : w in auts, x in UnitElements ];

  RF := recformat< n : Integers(),
  enhanced,
  GL4xGL4,
  GL4
  >
  ;

  enhancedimage:=[];
  for elt in enhanced_elements do 
    s := rec< RF | >;
    s`enhanced:=elt;
    s`GL4xGL4:=<NormalizingElementToGL4modN(elt`element[1],O,N: basis:=basis), UnitGroupToGL4modN((elt`element[2])`element,N : basis:=basis)>;
    s`GL4:=s`GL4xGL4[1]*s`GL4xGL4[2];
    Append(~enhancedimage,s);
  end for;


  semidirGL4:= sub< GL(4,ZmodN) |  [ x`GL4 : x in enhancedimage ] >;

  assert forall(u){ <s,t> : s in RandomSubset({1..#enhancedimage},10), t in RandomSubset({1..#enhancedimage},10) 
  | EnhancedElementInGL4(enhancedimage[s]`enhanced*enhancedimage[t]`enhanced) eq enhancedimage[s]`GL4*enhancedimage[t]`GL4 }; 

  return semidirGL4,enhancedimage;
end intrinsic;


intrinsic EnhancedImageGL4(AutmuO::Map, O::AlgQuatOrd, N::RngIntElt) -> GrpMat
  {return the image of the enhanced semidirect product group G in GL4(Z/NZ). The second return value 
  is a list of enhanced elements in record format.}

  OmodN:=quo(O,N);
  return EnhancedImageGL4(AutmuO, OmodN);
end intrinsic;


intrinsic EnhancedImageGL4(O::AlgQuatOrd, mu::AlgQuatElt, N::RngIntElt) -> GrpMat
  {return the image of the enhanced semidirect product group G in GL4(Z/NZ). The second return value 
  is a list of enhanced elements in record format.}

  AutmuO:=Aut(O,mu);
  assert MapIsHomomorphism(AutmuO);
  OmodN:=quo(O,N);
  return EnhancedImageGL4(AutmuO, OmodN);
end intrinsic;

intrinsic EnhancedImageGL4(O::AlgQuatOrd, mu::AlgQuatOrdElt, N::RngIntElt) -> GrpMat
  {return the image of the enhanced semidirect product group G in GL4(Z/NZ). The second return value 
  is a list of enhanced elements in record format.}

  AutmuO:=Aut(O,mu);
  assert MapIsHomomorphism(AutmuO);
  OmodN:=quo(O,N);
  return EnhancedImageGL4(AutmuO, OmodN);
end intrinsic;



intrinsic AutmuOinGL4modN(AutmuO::Map,O::AlgQuatOrd,N::RngIntElt : basis:=[]) -> GrpMat 
  {Embed AutmuO inside GL4(Z/NZ)}  
  if basis eq [] then 
    basis:=Basis(O);
  end if; 
  elts:=[ NormalizingElementToGL4modN(AutmuO(s),O,N : basis:=basis) : s in Domain(AutmuO) ];
  group:= sub< GL(4,ResidueClassRing(N)) | elts >;
  assert #group eq #elts;
  return group;
end intrinsic;


intrinsic AutmuOinGL4modN(O::AlgQuatOrd,mu::AlgQuatElt,N::RngIntElt : basis:=[]) -> GrpMat 
  {Embed AutmuO inside GL4(Z/NZ)} 
  AutmuO:=Aut(O,mu);
  return AutmuOinGL4modN(AutmuO,O,N);
end intrinsic;

intrinsic AutmuOinGL4modN(O::AlgQuatOrd,mu::AlgQuatOrdElt,N::RngIntElt : basis:=[]) -> GrpMat 
  {Embed AutmuO inside GL4(Z/NZ)} 
  AutmuO:=Aut(O,mu);
  return AutmuOinGL4modN(AutmuO,O,N);
end intrinsic;



