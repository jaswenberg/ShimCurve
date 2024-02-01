
intrinsic mod2Galoisimage(C::CrvHyp) -> GrpMat
    {Compute the mod 2 image of Jac(C) in GL(4,2)}

    G2 := Sp(4,GF(2));
    S6 := Sym(6);
    bool, phi := IsIsomorphic(S6, G2);

    somesubsG2 := Subgroups(G2 : OrderEqual := 48);
    somesubsS6 := Subgroups(S6 : OrderEqual := 48);  //there's two of them.
    A := AutomorphismGroup(G2);
    assert exists(out_aut){g : g in Generators(A) | not IsInner(g)};

    if Dimension(Fix(GModule(somesubsG2[1]`subgroup))) ne 0 then
        somesubsG2 := Reverse(somesubsG2);
    end if;
    if #Orbits(somesubsS6[1]`subgroup) eq 2 then
        somesubsS6 := Reverse(somesubsS6);
    end if;

    if IsConjugate(G2, somesubsG2[1]`subgroup, phi(somesubsS6[1]`subgroup)) then
        goodphi := phi;
    else
        goodphi := phi*out_aut;
    end if;


    C1 := SimplifiedModel(C);
    f := HyperellipticPolynomials(C1);

    if Degree(C) eq 6 then  
      gal:=GaloisGroup(f);
    else  
      gens5:=[ Eltseq(A) : A in Setseq(Generators(GaloisGroup(f))) ];
      gens6:=[ Sym(6)!(A cat [6]) : A in gens5 ];
      gal:=sub< Sym(6) | [ A : A in gens6 ] >;
    end if; 

    mod2img := goodphi(gal);
    return mod2img;

end intrinsic;