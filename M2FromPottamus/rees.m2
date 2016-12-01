--Takes an ideal I in a polynomial ring R, and a matrix f over R,
--and returns the definining ideal (in a new polynomial ring)
--of the Rees ring of the image of f, regarded as a matrix over R/I.

symmetricKernel=(I,f)->(
     R:=ring I;
     oldvarlist:=flatten entries vars R;
     nR:=rank source vars R;
     mtar:=-(min flatten degrees target f)+1;
     msource:=-(min flatten degrees source f)+1;
     tardeglist:=degrees source vars R | degrees target (f**R^{-mtar});
     Rtar1:=kk[oldvarlist,Y_1..Y_(rank target f),Degrees=>tardeglist];
--
--     sourcedeglist=degrees source vars R | degrees source (f**R^{-msource});
--     Rsource:=kk[oldvarlist, X_1..X_(rank source f),Degrees=>sourcedeglist];
--
     oldvars1:=(vars Rtar1)_{0..nR-1};
     Itar:= substitute(I,oldvars1);
     Rtar = Rtar1/Itar;
--
     ntarf:=rank target f;
     oldvars := (vars Rtar)_{0..nR-1};
     RtoRtar := map(Rtar, R, oldvars);
     g:=oldvars|((vars Rtar)_{nR..(nR+ntarf-1)})*(RtoRtar(f**R^{-mtar}));
--
     Rsource:=kk[oldvarlist,X_1..X_(rank source f),
	  Degrees=>degrees source g];
     i:=ideal mingens ker map(Rtar, Rsource, g);
     Ranswer:=kk[oldvarlist,X_1..X_(rank source f),
	  Degrees=>(degrees source oldvars)|toList((rank source f):{1})];
     substitute(i, Ranswer)
     )


--the following takes an ideal I in a polynomial ring R
--and a matrix f over R
--and returns the universal embedding of image (f ** R/I),
--written as a matrix over R

universalEmbedding=(I,f)->(
     R:=ring f;
     Rbar=R/I;
     fbar:=substitute(f, Rbar);
     fres:=res(image fbar, LengthLimit=>2);
     ftres:=res(image transpose fres.dd_1, LengthLimit=>2);
     fnew:=transpose ftres.dd_1;
     substitute(fnew, R)
     )

--compute the rees algebra of (coker f)**R/I

rees=(I,f)->symmetricKernel(I,universalEmbedding(I,f))

-- the case of an ideal i in a poly ring: I=0, f = gens i.
reesClassic= i->symmetricKernel(ideal(0_(ring i)),gens i)

--We can use this to compute the distinguished subvarieties of
--a variety (components of the support of the normal cone).
--In the following routine i must be an ideal of a polynomial ring, not a 
--quotient ring.
distinguished= i->(
     J:=reesClassic i; -- the ideal of the Rees algebra
     II=substitute(i, ring J);
     L:=decompose (II+J);
apply(L,P->kernel(map((ring J)/P, R))))

--or even do this with multiplicities!
--In the following routine i must be an ideal of a polynomial ring, not a 
--quotient ring.

distinguishedAndMult= i ->(
     J:=reesClassic i; -- the ideal of the Rees algebra
     I:=J+substitute(i, ring J); -- the ideal of the normal cone
     Itop:=top I; -- we only need the irreducibles of codim 1 mod J.
     L:=decompose (I); -- find its irred components
     apply(L,P->(Pcomponent:=Itop:(saturate(Itop,P)); 
	       --the P-primary component. The multiplicity is
	       --(degree Pcomponent)/(degree P)
       	  {(degree Pcomponent)/(degree P), kernel(map((ring P)/P, R))})))



specialFiber=(I,f)->(
--Produces the ideal, in a new polynomial ring, of the special
--fiber of the Rees algebra of R/I**(coker f).
     J:=rees(I,f);
     R:=ring I;
     nR:=rank source vars R;
     msource:=-(min flatten degrees source f)+1;
     fiberdeglist:= degrees source (f**R^{-msource});
     Rfiber:=kk[X_1..X_(rank source f),Degrees=>fiberdeglist];
     specialize:=map(Rfiber,ring J);
     trim (specialize J))

analyticSpread = (I,f) -> dim specialFiber(I,f)
--Produces the analytic spread of the module I
--fiber of the Rees algebra of R/I**(coker f).

isLinearType = (I,f) ->(
     --Let M be the image of f, regarded as a map over R/I.
     --The program  returns true iff the rees algebra of M
     --is equal to the symmetric algebra of M. Does so by
     --testing whether
     --the rees relations are linear forms in the new vars.
     K:=rees(I,f);
     T:=ring K;
     oldvars:=substitute(vars ring I, T);
     newvars:=compress ((vars T)%oldvars);
     test:=compress contract(newvars,contract(newvars, gens K));
     (rank source test)==0
     )

end

///
restart
load( "rees.m2")
kk=ZZ/32003
R=kk[a..e]
j=monomialCurveIdeal(R, {1,2,3,4})
I=ideal(0_R)
IR=rees(I,gens j)
degrees ring IR
betti gens IR
show IR
degrees source vars ring IR
SIR=specialFiber(I, gens j)
show SIR
dim SIR
analyticSpread(I, gens j)
----
restart
load( "rees.m2")

R=kk[x_1..x_8]
m1=genericMatrix(R,x_1,2,2)
m2=genericMatrix(R,x_5,2,2)
m=m1*m2
flatten m
i= ideal flatten m
d1=minors(2,m1)
d2=minors(2,m2)
j=i+d1+d2
codim j
d1_0
m_(0,0)
M=matrix{{0,d1_0,m_(0,0),m_(0,1)},
         {0,0,m_(1,0),m_(1,1)},
	 {0,0,0,d2_0},
	 {0,0,0,0}}
M=M-(transpose M)
minors(4,M)

I=ideal(0_R)
N=transpose (res coker transpose M).dd_2

uN=universalEmbedding(I,N)
symmetricKernel(I,uN)
IR=rees(I,N)

SIR=specialFiber(I, N)
///
///
fu=universalEmbedding(I,f)
betti symmetricKernel(I,fu)
betti symmetricKernel(I,f)
///
///
restart
load "rees.m2"
R=kk[x,y,z]
i=intersect(ideal(x),(ideal(x,y))^2, (ideal(x,y,z))^3)
distinguished i
use R
i
distinguishedAndMult i
///

restart
load "rees.m2"
load "reesAlgebra.m2"

kk=ZZ/101
R=kk[x,y,z]
i=ideal"xyz,x3y,y2z2"
S=kk[x,y,z,u,v,w,Degrees=>{3:{1,0},{3,1},{4,1},{4,1}}]
T=kk[x,y,z,t,Degrees=>{3:{1,0},{0,1}}]

reesClassic (ideal(0_(ring i),i))
j=gens (t*substitute(i,T))
degrees j
f=map(T,S,(vars T)_{0..2}|j)
kernel f
help "kernel(RingMap)"
degrees j
degrees S
degrees T
numgens ring i
ring i
restart
rees3= i->(
     m=syz gens i;
     R=ring i;
     S=(coefficientRing R)[X_0..X_(numgens R-1),Y_0..Y_(numgens i-1), 
	  Degrees=>toList (numgens R:{1,0})|apply(numgens i, p->flatten{degree i_p,1})];
     M=(f=map(S,R,matrix{{S_0..S_(numgens R-1)}})) m;
     K=ideal(matrix{{Y_0..Y_(numgens i -1)}}*M);
     saturate(K,f i_0)
     )
restart
kk=ZZ/101
RU=kk[x,y,z]
i=ideal"xyz,x3y,y2z2"

flatten{toList (numgens R:{1,0})|apply(numgens i, p->flatten{degree i_p,1})}

rees3 i

