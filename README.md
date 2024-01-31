The code in this repo is for Shimura curves with level structure. It can be used to compute invariants such as the genus, write the invariants to a formatted string and read data directly into MAGMA from text files if stored for those paramaters.

Fix (O,\pm mu,N) where O is (a maximal) order in an indefinite rational quaternion algebra B, mu is a polarized element and N is an integer. 

In analogy with the H < GL_2(Z/NZ) for modular curves, there is a H which depends on on the triple above and has an associated Shimura curve X_H. This requires some more explanation: 
- Let \Aut_{\pm \mu}(O) be the automorphisms of O which preserve \pm \mu
- (O/N)^x is just the units of the ring O/N
- G = \Aut_{\pm \mu}(O) \ltimes (O/N)^x, with the semidirect product naturally defined.

G plays the role of GL_2(Z/NZ), (O/N)^x is where the Galois representation lives if the surface has QM defined already and \Aut_{\pm \mu}(O) is like refined Atkin-Lehner involutions. A "PQM surface" has its Galois representatin contained in G, this is called the enhanced representation, see section 3.5 of https://arxiv.org/abs/2308.15193 for more details.

Types

Since it is not straightforward to work with G directly in MAGMA, new 'types' have been created to support it. These are:
- AlgQuatProj :: B^x/Q^x, the quaternion algebra modulo scalars :: QuaternionAlgebraModuloScalars(B::AlgQuat)
- AlgQuatProjElt :: an element of AlgQuatProj :: ElementModuloScalars(BxmodFx::AlgQuatProj, x::AlgQuatElt)
- AlgOrdRes :: O/N :: quo(O::AlgQuatOrd, N::RngIntElt)
- AlgOrdResElt :: an element of AlgOrdRes :: OmodNElement(OmodN::AlgQuatOrdRes, x::AlgQuatOrdElt)
- AlgQuatEnh :: the semidirect product G, allows for N=0 :: EnhancedSemidirectProduct(O::AlgQuatOrd: N:=0)
- AlgQuatEnhElt :: an element of G :: EnhancedElement(Ocirc::AlgQuatEnh, tup::<>)

Example usage:
> B<i,j>:=QuaternionAlgebra<RationalField() | 3, -1>;
> O:=MaximalOrder(B);
> BxmodQx:=QuaternionAlgebraModuloScalars(B);
> OmodN:=quo(O,3);
> w:=BxmodQx!(-3*j+3*i*j);
> w^2;
18
> w^2 eq BxmodQx!1;
true 18
> Genh:=EnhancedSemidirectProduct(O: N:=3);
> x:=OmodN!2;
> Genh!<w,x>
> ;
<-3*j + 3*k, [2 0 0 0]>
> Genh!<1,1> eq (Genh!<w,x>)^2;
true


Main Intrinsics

intrinsic HasPolarizedElementOfDegree(O::AlgQuatOrd,d::RngIntElt) -> BoolElt, AlgQuatElt 
  {return an element mu of O such that mu^2 + d*disc(O) = 0 if it exists.}

intrinsic IsTwisting(O::AlgQuatOrd,mu::AlgQuatElt) -> BoolElt
  {(O,mu) is twisting (of degree del = -mu^2/disc(O)) if there exists chi in O and N_Bx(O)
   such that chi^2 = m, m|Disc(O) and mu*chi = -chi*mu. Return true or false; if true 
   return [mu, chi] up to scaling}
   
intrinsic Aut(O::AlgQuatOrd,mu::AlgQuatElt) -> Any
  {Return Aut_{\pm mu}(O). It will be a map from D_n to B^x/Q^x where the codomain 
  is Aut_{\pm mu}(O)}

intrinsic NormalizingElementToGL4(w::AlgQuatElt,O::AlgQuatOrd: basis:=[]) -> GrpMatElt 
intrinsic NormalizingElementToGL4modN(w::AlgQuatElt,O::AlgQuatOrd, N::RngIntElt : basis:=[]) -> GrpMatElt 
  {O is an order over R. For an element g \in N_Bx(O) the map phi_g : b |--> g^-1bg
  is R-linear hence [g] is an element of M_4(R) after fixing a basis
  this function computes [g] and also returns the R-basis of O.}

intrinsic UnitGroupToGL4(x::AlgQuatOrdElt : basis:=[]) -> GrpMatElt 
intrinsic UnitGroupToGL4modN(x::AlgQuatOrdElt,N::RngIntElt : basis:=[]) -> GrpMatElt 
  {O is an order over R, this returns a matrix [lambda_g] wrt to a basis
  which is the right regular representation
  lambda_x : y --> y*x where g \in GL_1(O)}

intrinsic EnhancedSemidirectInGL4(Ocirc::AlgQuatEnh : basis:=[]) -> Map 
  {create the map from the semidirect product to GL4(R). R depends on the base 
  ring of Ocirc.}

intrinsic EnhancedElementInGL4(g::AlgQuatEnhElt : basis:=[]) -> GrpMatElt
  {the enhanced element in GL4(R), R depends on the base ring of g}

intrinsic EnhancedElementRecord(elt::AlgQuatEnhElt : basis:=[]) -> Any
  {given <w,x> in Autmu(O) \rtimes (O/N)^x or Autmu(O) \rtimes O^x  return <w,x> as a 
  record along with its embedding in GL_4xGL_4 and just GL_4}

intrinsic EnhancedImageGL4(AutmuO::Map, OmodN::AlgQuatOrdRes) -> GrpMat
  {return the image of the enhanced semidirect product group G in GL4(Z/NZ). The second return value 

intrinsic NormalizerPlusGenerators(O::AlgQuatOrd) -> SeqEnum 
  {return generators of the positive norm elements which normalize O}

intrinsic SemidirectToNormalizerKernel(O::AlgQuatOrd,mu::AlgQuatOrdElt) -> SeqEnum 
  {return the kernel of the map form the enhanced semidirect product to N_B^x(O). 
  It is necessarily cyclic and the second value is the generator of the group}

intrinsic NormalizerPlusGeneratorsEnhanced(O::AlgQuatOrd,mu::AlgQuatOrdElt) -> Tup 
  {return generators of the positive norm elements which normalize O in the enhanced semidirect product}

intrinsic EnhancedRamificationData(H::GrpMat, G::GrpMat,O::AlgQuatOrd,mu::AlgQuatElt) -> Any
  {return the image of the elliptic elements under the monodromy map}

intrinsic EnhancedGenus(sigma::SeqEnum) -> RngIntElt
  {Compute genus from permutation triple
   f:X -> Y. 2gX-2 = deg(f)*(2gY-2) + sum_x\inX (ex -1). 
   ex is the ramification degree of x. An element of S_n acts on sheets of the cover. 
  x is ramified if x is sent to another point under the action of an isotropy subgroup,
  i.e. the cycle type corresponding to x has length >1. The length is the ramification degree.}



