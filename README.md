The code in this repo is for Shimura curves with level structure. It can be used to compute invariants such as the genus, write the invariants to a formatted string and read data directly into MAGMA from text files if stored for those paramaters.

Fix (O,\pm mu,N) where O is (a maximal) order in an indefinite rational quaternion algebra B, mu is a polarized element and N is an integer. 

In analogy with the H < GL_2(Z/NZ) for modular curves, there is a H which depends on on the triple above and has an associated Shimura curve X_H. This requires some more explanation. 
- Let \Aut_{\pm \mu}(O) be the automorphisms of O which preserve \pm \mu
- (O/N)^x is just the units of the ring O/N
- G = \Aut_{\pm \mu}(O) \ltimes (O/N)^x, with the semidirect product naturally defined.

G plays the role of GL_2(Z/NZ), (O/N)^x is where the Galois representation lives if the surface has QM defined already and \Aut_{\pm \mu}(O) is like refined Atkin-Lehner involutions. A "PQM surface" has its Galois representatin contained in G, this is called the enhanced representation, see section 3.5 of https://arxiv.org/abs/2308.15193 for more details.

Types

Since it is not straightforward to work with G directly in MAGMA, new 'types' have been created to support it. These are:
- AlgQuatProj:: B^x/Qx, the quaternion algebra modulo scalars
- AlgQuatProjElt:: an element of AlgQuatProj


