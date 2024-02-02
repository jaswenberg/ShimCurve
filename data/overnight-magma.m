
for N in [3,4,6] do 
	for del in [1,2] do 
        rhocirc:=EnumerateH(6,del,N : PQMtorsion:=false, verbose:=true, minimal:=false, lowgenus:=false, write:=true);
    end for;
end for;

