The code in this repo is for Shimura curves with level structure. It can be used to compute invariants such as the genus, write the invariants to a formatted string and read data directly into MAGMA from text files if stored for those paramaters.

Fix (O,\pm mu,N) where O is (a maximal) order in an indefinite rational quaternion algebra B, mu is a polarized element and N is an integer. 

In analogy with the H < GL_2(Z/NZ) for modular curves, there is a H which depends on on the triple above and has an associated Shimura curve X_H. This requires some more explanation. 
- Let \Aut_{\pm \mu}(O) be the automorphisms of O which preserve \pm \mu
- (O/N)^x is just the units of the ring O/N
- G = \Aut_{\pm \mu}(O) \ltimes (O/N)^x
