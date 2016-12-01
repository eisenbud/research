restart
--Example of a 2-regular var with plane section a surface
--(plane with emb comp at 0) that is not even linearly
--presented.
--It's the cone over the 

S=kk[a,b,d,e]
Nilp3=matrix{{a,b,0},{0,a,b}}
Scroll1=matrix{{d},{e}}
m=Nilp3|Scroll1
i=minors(2,m)
betti res i
--o19 = total: 1 6 9 5 1
--          0: 1 . . . .
--          1: . 6 8 3 .
--          2: . . 1 2 1
--Nilp3|Scroll1 
--is quadratically generated, not linearly presented. Codim 2 in 4 vars, with
--emb comp; cone over a curve, with emb pt at vertex
j=radical i
j=saturate i -- j=(a,b) = radical i
betti res (N= ((module j)/(module i)))
apply(0..3,i->hilbertFunction(i,N)) -- its (0,2,1,0), generated in deg 1.

----------------------
--In general, Michael Catalano Johnson proved that
--a nilpotent block of size beta (means beta vars, beta+1 cols)
--followed by a scroll block of size alpha gives something with regularity
--max(2, 1+greatest int in beta/alpha).

Nilp2=matrix{{a,0},{0,a}}
m=Nilp4|Scroll1
i=minors(2,m)
betti res i

ma=a*id_(S^2)
mb=b*id_(S^2)
Nilp4=matrix{{a,b,c,0},{0,a,b,c}}
Scroll2=matrix{{d,e},{e,f}}
m=Nilp4|Scroll2
--Nilp4|Scroll2
--satisfies N(2,2), not N(2,3), and its a curve (to make it saturated, need surf).

help genericMatrix

restart
--2x4 case
S=kk[a..h]
gen4=transpose genericMatrix(S,a,4,2)
FF=res (M= ((S^1)/ minors(2,gen4)))
T=kk[u,v,x,y]
phi=map(T,S,{u,v,x,y,
	     x,y,0,0})
TFF=phi FF
N=coker TFF.dd_1
GG=res N
betti GG
f=extend(GG,TFF,map(GG_0,TFF_0))
prune coker f

--betti prune coker f -- gives an error when the answer is really 0

--2x5 case
restart
S=kk[a..j]
gen=transpose genericMatrix(S,a,5,2)
FF=res (M= ((S^1)/ minors(2,gen)))
T=kk[u,v,x,y,z]
phi=map(T,S,{u,v,x,0,y,
	     0,u,v,x,z})
TFF=phi FF
N=coker TFF.dd_1
GG=res N
betti GG
f=extend(GG,TFF,map(GG_0,TFF_0))
prune coker f
betti prune coker f
