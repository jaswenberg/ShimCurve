_<x> := PolynomialRing(Integers());
primeB := 100;

myGcd := function(ptcnts);
  ptcnts0 := [v : v in ptcnts | v[2] ne 0];
  s1 := Gcd(ptcnts0[1][2],ptcnts0[2][2])
        *ptcnts0[1][1]^Valuation(ptcnts0[2][2],ptcnts0[1][1])
        *ptcnts0[2][1]^Valuation(ptcnts0[1][2],ptcnts0[2][1]);
  if s1 eq 1 then return 1; end if;
  return &*[p[1]^Min([Valuation(ptcnts[j][2],p[1]) : j in [1..#ptcnts] | ptcnts[j][1] ne p[1]]) : p in Factorization(s1)];  
end function;

strtochar := function(str);
  d := Split(str, " ")[3];
  return KroneckerCharacter(StringToInteger(d));
end function;

makemat := function(Tp, V);
  MTp := Matrix([v*Tp : v in Basis(V[1])]);
  Vmat := Matrix(Basis(V[1]));
  cols := [];
  rownum := 1;
  colnum := 1;
  while rownum le Dimension(V[1]) do
    if Vmat[rownum,colnum] eq 0 then
      colnum +:= 1;
    else
      assert Vmat[rownum,colnum] eq 1;
      Append(~cols,colnum);
      rownum +:= 1;
      colnum +:= 1;
    end if;
  end while;
  TpV := ColumnSubmatrix(MTp,cols);
  return TpV;
end function;

defPQM := [* *];
MDs := [];
for V in probPQM do
  print Index(probPQM, V);
  N := V[1];
  psi := V[2];
  if Type(psi) eq MonStgElt then
    psi := strtochar(psi);
  end if;
  apfs := V[3];
  aps := [<v[1], Roots(v[2])[1][1]> : v in apfs | Degree(v[2]) eq 1];
  for D in Sort(Divisors(N)) do 
    if D eq N then
      Append(~defPQM, [* D, V[2], V[3] *]);
      break;
    end if;
    Dind := Index([MD[1] : MD in MDs], D);
    if Dind eq 0 then
      time M := ModularSymbols(D,2,-1);
      Append(~MDs, <D, M>);
    else
      M := MDs[Dind][2];
    end if;
    printf "D = %o = %o, dim(M_2) = %o\n", D, Factorization(D), Dimension(M);
    if Dimension(M) eq 0 then continue; end if;
    VQQ := Kernel(HeckeOperator(M,aps[1][1])-aps[1][2]);
    if Dimension(VQQ) le 2 then continue; end if;
    for ap in aps do
      printf "p = %o\n", ap[1];
      time Tp := HeckeOperator(M,ap[1]);
      TpVQQ := makemat(Tp, [VQQ]);
      KTpVQQ := Kernel(TpVQQ - ap[2]);
      VQQ := sub<VQQ | Rows(Matrix(Basis(KTpVQQ))*Matrix(Basis(VQQ)))>;
      if Dimension(VQQ) lt 2 then break; end if;
    end for;
    if Dimension(VQQ) lt 2 then 
      continue; 
    else
      ap2s := [v3 : v3 in V[3] | Degree(v3[2]) eq 2];
      for v in ap2s do
        printf "p = %o\n", v[1];
        time Tp := HeckeOperator(M,v[1]);
        TpVQQ := makemat(Tp, [VQQ]);
        KTpVQQ := Kernel(Evaluate(v[2],TpVQQ));
        VQQ := sub<VQQ | Rows(Matrix(Basis(KTpVQQ))*Matrix(Basis(VQQ)))>;
        if Dimension(VQQ) lt 2 then break; end if;
      end for; 
      assert Dimension(VQQ) eq 2;
      Append(~defPQM, [* D, V[2], V[3] *]);  
      break;
    end if;
  end for;
end for;

for V in probPQM do
  N := V[1];
  K := SplittingField([v3[2] : v3 in V[3]]);
  delta := Discriminant(Integers(K));
  // psi := strtochar(V[2]);
  psi := V[2];
  psicond := KroneckerDiscriminant(psi);
  printf "%o & %o & %o & ", V[1], psicond, 
    Discriminant(QuaternionAlgebra(Rationals(),psicond,delta));

  ps := [p : p in PrimesUpTo(primeB) | Gcd(N,p) eq 1];
  apchars := Sort(V[3]);
  ptcnts := [];
  for i := 1 to #ps do
    p := ps[i];
    assert apchars[i][1] eq p;
    fp := apchars[i][2];
    if psi(p) eq 1 then 
      assert Degree(fp) eq 1; 
      ap := -Evaluate(fp,0);
      Append(~ptcnts, <p,Evaluate((x^2-ap*x+p)^2,1)>);
      // print p, x^2-ap*x+p;
    else
      assert psi(p) eq -1; 
      assert Degree(fp) eq 2 and Coefficient(fp,1) eq 0; 
      ap2 := -Evaluate(fp,0);
      Append(~ptcnts, <p,Evaluate(x^4+(2*p-ap2)*x^2+p^2,1)>);
      // print p, x^4+(2*p-ap2)*x^2+p^2;
    end if;
  end for;
  torsord := myGcd(ptcnts); 
  printf "%o & ", torsord;

  apfs := V[3];
  aps := [<v[1], Roots(v[2])[1][1]> : v in apfs | Degree(v[2]) eq 1];
  for ap in aps do 
    if Index(aps,ap) ne 1 then printf ", "; end if; 
    printf "a_{%o} = %o", ap[1], ap[2];
  end for;
  printf " \\\\ \n";
end for;
