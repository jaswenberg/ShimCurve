for D in [6] do
  for N in [6] do 
    for del in [6] do 
	  rhocirc:=AllEnhancedSubgroups(D,del,N : PQMtorsion:=false, verbose:=true, minimal:=false, lowgenus:=false, write:=true);
	  print "";
	end for;
  end for;
end for;
