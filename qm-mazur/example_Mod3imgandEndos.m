AttachSpec("spec");
G := GSp(4,3);
assert exists(SG){x`subgroup : x in Subgroups(G : OrderEqual := ExactQuotient(#G,2))};

// Consider the curve https://beta.lmfdb.org/Genus2Curve/Q/262144/d/524288/1
R<x> := PolynomialRing(Rationals()); C := HyperellipticCurve(R![-1, 5, -8, 4, -1, 1], R![]);
C := SimplifiedModel(C);
mod3imglbl, mod3img := mod3Galoisimage(C); #mod3img;
// 288

// All the endomorphisms are defined over Q(zeta_8), a degree 4 field, as per https://beta.lmfdb.org/Genus2Curve/Q/262144/d/524288/1,
end_rep := HeuristicEndomorphismRepresentation(C : Geometric := true);
endmats := [Transpose(ChangeRing(x[2],GF(3))) : x in end_rep];


assert &and[IsInvertible(x) : x in endmats];
end_subgrp := sub<GL(4,GF(3))|endmats>; #end_subgrp; // instead of (O/3O)^*, naively considering just the subgroup spanned by generators
Gl := GL(4,GF(3));
G := sub<Gl|[Eltseq(g) : g in Generators(G)]>;
end_subgrp subset G;
// false as expected because the basis used in endomorphism representation need not be symplectic
#Centralizer(G,end_subgrp) eq 72;
// false as expected



// We consider all change of basis
conjs := Conjugates(Gl,end_subgrp); #conjs;
// 2340
// and consider all possibilities for the mod-3 image over the endomorphism field
Z_subs := [x : x in NormalSubgroups(mod3img : OrderEqual := ExactQuotient(#mod3img,4)) | not x`subgroup subset SG]; #Z_subs;
// 4
{GroupName(quo<mod3img|x`subgroup>) : x in Z_subs};
// { C2^2 }

good_H := [];
good_endmatgrp := [];
for x in Z_subs do
    H := ChangeRing(x`subgroup,GF(3));
    for conj in conjs do
        if &and[&and[x*y eq y*x : y in Generators(conj)] : x in Generators(H)] then
            Append(~good_H,H);
            Append(~good_endmatgrp,conj);
        end if;
    end for;
end for;
#good_H, #good_endmatgrp;
// 1 1
// There is exactly one choice of basis, and mod-3 image over endomorphism field
// such that Galois and endomorphisms commute.

HH := good_H[1];
endmatgrp := good_endmatgrp[1];
HH eq Centralizer(HH,endmatgrp);
// true
IsConjugate(Gl,HH,endmatgrp);
/*
[1 0 0 0]
[2 1 2 0]
[1 0 2 0]
[0 0 0 1]
*/

