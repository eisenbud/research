
--The following returns the submodule generated by the degree d
--generators of the module A
submoduleByDegrees=(A,Deglist)->(
     F := target presentation A;
     L := flatten degrees F;
     L1:= toList select(0..(rank F)-1,i->member(L_i,Deglist));
     prune (image F_L1/(image presentation A)))


document{Key => submoduleByDegrees,
     Headline => "Submodule of A generatd by generators of degrees listed",
Inputs => {"A=>Module", "Deglisst=>List of ZZ"},
Usage => "SubmoduleByDegrees(A, Deglist)",
EXAMPLE lines ///
kk=ZZ/7
S=kk[a,b,c,d]
m=coker random(S^{2,4,6},S^{-1,3})
betti m
betti submoduleByDegrees(m, {-4,-5,-6})
///
}


--the following takes a matrix, and returns the submatrix
--whose rows are of degree d and whose columns are of degree e

----BUG???---- This doesn't work. 

submatrixByDegs=(f,D,E)->(
     --D,E are lists of degrees for rows and cols, respectively
     Ltarget := flatten degrees target f;
     Lsource := flatten degrees source f;
     Lt:= toList select(toList(0..(rank target f)-1),i->member(Ltarget_i, D));
     Ls:= toList select(toList(0..(rank source f)-1),i->member(Lsource_i, E));
     f_Lt^Ls
     )



document{Key => submatrixByDegs,
Headline => "submatrix of elements with given row and col degrees",
Inputs => {"(Matrix, List of ZZ, List of ZZ)"},
Usage => "submatrixByDegs(m, rowdegs, coldegs)",
EXAMPLE lines ///
kk=ZZ/2
S=kk[a,b,c,d]
m=random(S^{2,4,6},S^{-1,3})
betti m
n= submatrixByDegs(m,{3},{4})
betti n
n=submatrixByDegs(m,{-2,-4},{1})
betti n
///
}     

end
restart
load "select-by-degrees.m2"
