input("Davidsinit.m2")
-------- twisted cubics -------
kk=ZZ/101
S=kk[a,b,c,d]
E=kk[A,B,C,D,SkewCommutative=>true]
m=matrix(table(2,3,(i,j)-> S_(i+j)))
M=symExt(m,E)
fMt= res coker transpose M;
betti fMt
------- still wrong-------
-----------------------------
-------restricting double line------------
input("Davidsinit.m2")
E=kk[A,B,C,SkewCommutative=>true]
 
m=map(E^{-1,3:0},E^{-1,3:-2},matrix{{0,A,B,C},{A,0,0,0},{B,0,0,B*C},{C,-B*C,0,0}})
fm=res coker m
betti fm
n=map(E^5,E^{7:-1},matrix{{A,B,0,0,C,0,0},{0,A,B,0,0,C,0},{0,0,A,B,0,0,C},{0,0,0,0,A,B,0},{0,0,0,0,0,A,B}})
fn=res coker n
betti fn
fnt=res  coker transpose n
betti fnt
M=fnt.dd_3
betti M

U=kk[A,B,SkewCommutative=>true]


------------restrict----------
restrict = (M,U) -> (
-- M = presentation matrix of an E-module over 
--	some exterior algebra
-- U  = a subalgebra of E corresponding to a hyperplane,
-- 	ie. same letters occur for generators
-- h (not needed) in E a defining equation of the hyperplane,
-- 	identified with an element of E via the
-- 	given basis by generators
-- result = presentation matrix correponding the U-module 
--	N which correspond to the restriction.
E:=ring M;
u:=substitute(vars U,E);
h:=(vars E)*(syz contract(vars E,transpose u));
M11:=substitute(M,U);
M22:=substitute(substitute(M,U),-1_U*vars U)**U^{1};
M12:=substitute(contract(h_0_0,M),U)**U^{0};
N:=(M11||(0_U*M22)**U)|(M12||M22)
)

N=restrict(M,U)
betti N
isHomogeneous(N)
M1=syz M
N1=restrict(M1,U)
