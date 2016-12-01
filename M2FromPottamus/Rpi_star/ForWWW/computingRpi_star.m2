selectComponent=(L,k)->(apply(L,c->c#k))

load "betti-fix.m2"

bettiT=method()
bettiT(ChainComplex):=(F)->(
--writes the betti table of a bigraded Tate resolution (with the maps 
--going from right to left, as in the usual betti command)
--using the SECOND degrees instead of the first.
     a:=min F;b:=max F;
     btt:=ZZ/3[tt];
     bT:=new ChainComplex;
     bT.ring=btt;
     apply(a..b,i->bT#i=btt^(-selectComponent(degrees (F_i),1)));
     betti bT
     )     

degreeZeroPart=(T,A)->(
--Takes a (doubly) graded free complex over E (the exterior algebra 
--over a ring A, where the variables of E have grading {1,1} and {2*,0}) 
--and extracts the the degree {*,0} part of T \tensor_E A, 
--a complex of free A-modules.
--                  Berkeley, 18/12/2004, David Eisenbud, Frank Schreyer. 
     a:=min T;b:=max T;
     piT:=new ChainComplex;
     piT.ring=A;
     bj:=0;aj:=0;LLj:={};Lj:=LLj;co:={};ro:={};
     apply(a..b,j->(bj=rank T_j;
	       LLj=select(degrees T_j,d->d#1==0);
	       LLj=apply(LLj,d->-d);
	       piT#j=A^LLj));
     apply(a+1..b,j->(
	       aj=rank  T_(j-1);
	       bj=rank T_j;
	       Lj=degrees T_(j-1);
	       LLj=degrees T_(j);
	       co=toList select(0..aj-1,i->(Lj#i)#1==0);
	       ro=toList select(0..bj-1,i->(LLj#i)#1==0);
	       piT.dd#j=substitute(((T.dd_j)^co)_ro,A)));
     piT)

symmetricToExteriorOverA=method()
symmetricToExteriorOverA(Matrix,Matrix,Matrix):= (m,e,x) ->(
--this function converts between a  presentation matrix m with 
--entries m^i_j of degree deg_x m^i_j = 0 or 1 only 
--of a module over a symmetric algebra A[x] and the linear part of the
--presentation map for the module 
--    P=ker (Hom_A(E,(coker m)_0) -> Hom_A(E,(coker m)_1))
--over the  exterior algebra A<e>.
--                                 Berkeley, 19/12/2004, Frank Schreyer.
     S:= ring x; E:=ring e;
     a:=rank source m;
     La:=degrees source m;
     co:=toList select(0..a-1,i->  (La_i)_1==0);
     M0:=coker substitute(m_co,vars E);
     M:=coker m;
     m1:=presentation (ideal x * M);
-- script uses the fact that the generators of (ideal x)* M are ordered
---as follows
-- x_0 generators of M,x_1*generators of M, ...
     b:=rank source m1;
     Lb:=degrees source m1;     
     cob:=toList select(0..b-1,i->  (Lb_i)_1==1);
     M1:=coker substitute(m1_cob,vars E);
     F:=substitute(id_(target m),vars E);
     G:=e_{0}**F;
     n:=rank source e -1;
     apply(n,j->G=G|(e_{j+1}**F));
     phi:=map(M1,M0,transpose G);
     presentation prune ker phi)

     
end	      
restart

load "computingRpi_star.m2"
load "vectorBundlesOnPP1.m2"
L={1,3,5,7}
kk=ZZ/101
M=setupDef(L,kk)
N=symmetricToExteriorOverA(M,ee,xx)
fN=res(coker N,LengthLimit=>7)
bettiT dual fN
diags=apply(3..7,i->(
	  T=fN**E^{{0,i}};
	  Rpi=degreeZeroPart(T,A);
	  Rpi.dd_(i-1)))
apply(diags,d->bettiT chainComplex(transpose d))	  
diags_2
T=fN**E^{{0,3}}[2];



Rpi= degreeZeroPart(T,A)

bettiT dual(Rpi)
bettiT dual(T)
