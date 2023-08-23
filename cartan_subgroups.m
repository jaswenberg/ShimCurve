

intrinsic NonsplitCartan(p::RngIntElt) -> GrpMat, GrpMatElt
  {create the nonsplit Cartan subgroup of GL_2(Fp) and a generator}
  G:=GL(2,p);
  Fp:=GF(p);
  eps:=PrimitiveElement(Fp);
  elts:=[ G![x,eps*y,y,x] : x,y in Fp | [x,y] ne [0,0]];
  Cns:=sub< G|elts >;
  assert #Cns eq p^2-1;
  tr, del:=IsCyclic(Cns);
  return Cns, del;
end intrinsic;

intrinsic NonsplitCartanLabel(H::GrpMat) -> MonStgElt
  {return the lmfdb label of the subgroup of cartan subgroup}
  Fp:=BaseRing(H);
  p:=Characteristic(Fp);
  tr,delta:=IsCyclic(H);
  gens := [ delta^i : i in [1..#H] | sub<GL(2,Fp) | delta^i> eq H ];
  ab:=[ [Eltseq(A)[1],Eltseq(A)[3]] : A in gens ];
  Sort(~ab);
  return Sprintf("%oCn.%o.%o[%o]", p, ab[1,1], ab[1,2], DeterminantIndex(H));
end intrinsic;

intrinsic NormalizerNonsplitCartan(p::RngIntElt) -> GrpMat
  {create the normalizer of nonsplit Cartan subgroup of GL_2(Fp)}
  Cns:=NonsplitCartan(p);
  G:=GL(2,p);
  gamma:=G![1,0,0,-1];
  NCns:=sub< G | Cns, gamma >;
  assert #NCns eq 2*#Cns;
  return NCns;
end intrinsic;

intrinsic SubgroupMeetCentre(H::GrpMat) -> GrpMat
  {Intersect H with the centre of the matrix group}
  Fp:=BaseRing(H);
  G:=GL(2,Fp);
  eps:=PrimitiveElement(Fp);
  Z := sub < G | G![eps,0,0,eps] >;
  return H meet Z;
end intrinsic;


intrinsic SubgroupsOfNormalizerNonsplitCartan(p::RngIntElt) -> GrpMat
  {return subgroups and data of these normalizers that aren't contained in Nonsplit Cartan}
  list:=[];

  G:=GL(2,p);
  Cns,delta:=NonsplitCartan(p);
  gamma:=G![1,0,0,-1];

  RF := recformat< n : Integers(),
  Label,
  Characteristic,
  Order,
  Group,
  DeterminantIndex,
  IsSemidirect >;
  s := rec< RF | >;
  for i in Reverse(Divisors(#Cns)) do
    H:=sub< G | delta^i >;
    if Integers()!(#H/#SubgroupMeetCentre(H)) ne 1 then
      lb:=Split(NonsplitCartanLabel(H),"n")[2];
      s`Label:=Sprintf("%oNn%o",p,lb);
      s`Characteristic := p;
      s`Order:=Order(H);
      s`Group:= sub< G | H, gamma >;
      s`DeterminantIndex:= DeterminantIndex(H);
      s`IsSemidirect:=true;
      assert #s`Group eq 2*#H;
      Append(~list,s);
    end if;

    if DeterminantIndex(H) eq DeterminantIndex(SubgroupMeetCentre(H)) and
      G![-1,0,0,-1] in H then
      e:=Integers()!((p-1)/#SubgroupMeetCentre(H));
      lb:=Split(NonsplitCartanLabel(H),"n")[2];
      lb:=Split(lb,"[");
      s`Label:=Sprintf("%oNn%o.%o[%o]",p,lb[1],e,DeterminantIndex(H));
      s`Characteristic := p;
      s`Order:=Order(H);
      s`Group:= sub< G | H, gamma*(delta^e) >;
      s`DeterminantIndex:= DeterminantIndex(H);
      s`IsSemidirect:=false;
      assert #s`Group eq 2*#H;
      assert gamma notin s`Group;
      assert DeterminantIndex(H) ne 1;
      Append(~list,s);
    end if;

  end for;

  return list;
end intrinsic;

intrinsic DeterminantIndex(H::GrpMat) -> RngIntElt
  {Return index of Det(H) in F_p^x}
  Fp:=BaseRing(H);
  return Integers()!((#Fp-1)/#Set([ Determinant(A) : A in H ]));
end intrinsic;

/*
non_split:=[];
labels:=[];
for p in [ p : p in PrimesUpTo(11) | p ne 2 ] do
  list:=SubgroupsOfNormalizerNonsplitCartan(p);
  for group in list do
    if group`IsSemidirect eq false then
      Append(~non_split,group);
      Append(~labels,group`Label);
    end if;
  end for;
end for;
*/



/*
p:=11;
G:=GL(2,p);
Cns11,delta:=NonsplitCartan(p);
gamma:=G![1,0,0,-1];
H:=sub< G | delta^8, (delta^2)*gamma >;


RF := recformat< n : Integers(),
Order,
DeterminantIndex,
IsSemidirect >;
s := rec< RF | >;

s`Order:=4;
s`DeterminantIndex:=1;
s`IsSemidirect:=false;

list:=[];
Append(~list,s);



*/
