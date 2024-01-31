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




