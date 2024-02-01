
function monicquinticmodel(f,a);
    P<x> := Parent(f);
    g := P ! (Evaluate(f,a+1/x)*x^6);
    a5 := Coefficient(g,5);
    g := Evaluate(g,a5*x)/a5^6;
    assert IsIsomorphic(HyperellipticCurveOfGenus(2,f),HyperellipticCurveOfGenus(2,g));
    return g;
end function;


function fourtorsionfield(C : simplified := false);
    C1 := SimplifiedModel(C);
    f := HyperellipticPolynomials(C1);
    roo := Roots(f);
    if #roo ge 1 then
        newf := monicquinticmodel(f, roo[1,1]);
        C2 := HyperellipticCurveOfGenus(2,newf);
        K := SplittingField(f);
        roo := Roots(newf,K);
    else
        Fac := Factorisation(f);
        F<a> := NumberField(Fac[1,1]);
        newf := monicquinticmodel(ChangeRing(f,F), a);
        C2 := HyperellipticCurveOfGenus(2,newf);
        K, roos := SplittingField([h[1] : h in Fac]);
        FintoK := hom<F -> K | roos[1][1]>;
        PK<x> := PolynomialRing(K);
        PintoPK := hom<Parent(newf) -> PK | FintoK, x>;
        roo := Roots(PintoPK(newf),K);
    end if;

    listofrootdiffs := [K ! -1];
    for j := 1 to 4 do
        for k := j+1 to 5 do
            rootdiff := roo[j,1]-roo[k,1];
            Append(~listofrootdiffs,rootdiff);
        end for;
    end for;

    if not simplified then
        return f, listofrootdiffs;
    else
        if IsSquare(K ! -1) then
            gens_of_quadextns := [];
        else
            gens_of_quadextns := [K ! -1];
        end if;

        for i := 2 to #listofrootdiffs do
            alpha := listofrootdiffs[i];
            if #gens_of_quadextns eq 0 then
                if not IsSquare(alpha) then
                    Append(~gens_of_quadextns,alpha);
                end if;
            else
                binarystrings := VectorSpace(GF(2),#gens_of_quadextns);
                bool := true;
                for x in binarystrings do
                    a := alpha*&*[(x[j] eq 1) select gens_of_quadextns[j] else 1 : j in [1..#gens_of_quadextns]];
                    if IsSquare(a) then
                        bool := false;
                        break;
                    end if;
                end for;
                if bool then
                    Append(~gens_of_quadextns,alpha);
                end if;
            end if;
        end for;
        return f, gens_of_quadextns;
    end if;
end function;


// Example

/*R<x> := PolynomialRing(Rationals());
C := HyperellipticCurve(R![0, 0, 0, 0, 1, 1], R![1, 1, 0, 1]);
twotorspol, gens := fourtorsionfield(C);
twotorspol, #gens;
twotorspol, gens := fourtorsionfield(C : simplified := true);
twotorspol, #gens;*/
