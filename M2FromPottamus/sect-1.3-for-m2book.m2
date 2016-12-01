restart

kk = ZZ/32003
S = kk[a,b,c,d]
I = ideal(a*c-b^2, a*d-c*b, b*d-c^2)
A = S/I
f = matrix{{- d, 0, 0, - c, - d, 0, - b, - c, - d}, 
           {c, - d, 0, b, 0, - d, a, 0, 0}, 
	   {0, c, - d, 0, b, 0, 0, a, 0}, 
	   {0, 0, c, 0, 0, b, 0, 0, a}}
M = coker f

S=kk[a,b,c]

use S
alpha=map(S^1, S^{3:-1}, {{a,b,c}})
M=ker alpha
beta=generators M
gamma=presentation M
F=res coker alpha
F.dd
beta1=F.dd_2
beta
dim singularLocus ideal random(5,S)
S=kk[a,b,c]
<<<iPoint1=ideal(a,b)>>>
<<<iPoint2=ideal(a,c)>>>
<<<iPoint3=ideal(b,c)>>>
<<<iPoint4=ideal(a-b,b-c)>>>

point=ideal(b,c)
inclusion = gens(point^2)
degrees source inclusion
degrees S^{3:-2}
degrees target inclusion

betti inclusion
randomMap=random(S^{3:-2}, S^{-6})
randomMap=random(source inclusion, S^{-6})
idealC2=ideal(inclusion*randomMap)
sing = singularLocus idealC2
singIdeal=ideal presentation sing
saturate singIdeal

quadrics=map(S^1, module point)*basis(2,module point)
R2=S/idealC2
linSer=substitute(quadrics, R2)
T=kk[x_0..x_4]
idealC4=kernel map(R2,T,linSer)
betti idealC4

idealC4 = trim idealC4
betti idealC4
F=res idealC4
betti F
deg2places = positions(degrees source gens idealC4, 
     i->first i==2)
idealScroll= ideal (gens idealC4)_deg2places
codim idealScroll
degree idealScroll
G=res idealScroll
betti G
G.dd
M=G.dd_2
minors(2, M)
idealScroll
J=jacobian idealC4
c=codim idealC4
codim (idealC4+minors(3,J))
R4=T/idealC4
--dimension singularLocus R4
singularLocus R4

R4=T/idealC4
f=vars R4
g=substitute( jacobian gens idealC4, R4)
cotan1=homology(f,g)
presentation cotan1
cotan1=prune cotan1
betti cotan1
T^1/idealC4
cotan2 = Ext^3(T^1/idealC4, T^{-5})
cotan2 = prune cotan2
cotanSheaf2=sheaf cotan2
canonicalModule=HH^0(cotanSheaf2)
cotan=substitute(cotan2, R4)
canonicalSections=basis(0,cotan)
genus = rank source canonicalSections
dualModule = Hom(cotan, R4^1)
f = homomorphism map(dualModule, R4^{-1},{{1},{0},{0}} )
canGens=f*basis(0,cotan)
S8=kk[x_0..x_8]
idealC8 = trim kernel map(R4,S8,canGens)
betti idealC8
  
				    