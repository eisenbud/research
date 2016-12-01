--Hartshorne's question: what's the Clifford index
--of a general linear determinantal curve in P3?

restart
kk=ZZ/32003

S=kk[w,x,y,z]
n=5
m=random(S^n,S^{n+1:-1})
--try a special, more sparse matrix
m1=matrix{{w,x,y,z,0,0},
     	 {0,w,x,y,z,0},
	 {0,0,w,x,y,z}}
m2=random(S^2,S^{6:-1})
m=m1||m2
betti m

--even more degenerate
m=matrix{{w,x,y,z,0,0},
     	 {0,w,x,y,z,0},
	 {0,0,w,x,y,z},
	 {z,0,0,w,x,y},
	 {y,z,0,0,w,x}}
    
iC=minors(n,m)
codim iC
omega=coker(m**S^{2})
-- compute the genus 
g=rank source basis(0,omega)
--re-embed C in canonical space
dualmodule=Hom(omega, S^1/iC)
f=homomorphism dualmodule_{0}
cangens=f*basis(0, omega)
betti cangens
T=kk[a_1..a_g]
SC=S/iC
ican=kernel map(SC, T, substitute(cangens, SC))

betti res(ican, LengthLimit=10, DegreeBound=>2
