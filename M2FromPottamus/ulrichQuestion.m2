restart
input "herzogFaktorization.m2"
d=3
primar=factor (5^d-1)
e=#primar
prim=primar#(e-1)
p=prim#0
kk=ZZ/p
rho= matrix(apply(d-1,i->apply(d-1,j->if j<d-2 then 
	       (if j+1==i then 1 else 0) else -1)))
sum(d,i->rho^i)
rho^d
rho=matrix{{5}}

n=2*d
R=kk[x_0..x_n]
rho=substitute(rho,R)
L=flatten entries ((vars R)_{0..d-1})
L2=flatten entries ((vars R)_{d..2*d-1})

psi=apply(L,x->matrix{{x}})
psi2=herzog(psi,rho,L2);
betti psi2#1
PP=product(psi2);
(PP_{0}^{0}**id_(target PP))==PP
psi2

R=kk[x_0..x_5]
rho=substitute(rho,R)
M=substitute(genericSymmetricMatrix(R,x_0,3),matrix{{x_0,x_1,x_2,x_2+x_3,x_4,x_5}})

P=x_0*x_5-x_1*x_4+x_2*x_3
F=det M
F1=F+2*x_2*P
L1={x_2,x_2,x_3-x_2}
L2={x_0,-x_4,x_4}
L3={x_1,-x_1,x_5}
L4={x_0,3*x_2+x_3,x_5}
phi1=apply(L1,x->matrix{{x}})
phi2=herzog(phi1,rho,L2)
phi3=herzog(phi2,rho,L3)
phi=herzog(phi3,rho,L4);
betti phi#0
PP=product(phi);
(PP_{0}^{0}**id_(target PP))==PP
PP_{0}^{0}==F1

E=kk[y_0..y_3,SkewCommutative=>true]
N=substitute(phi#0,matrix{{y_0*y_1,y_0*y_2,y_0*y_3,y_1*y_2,y_1*y_3,y_2*y_3}});
betti N
betti(N=map(E^27,E^{27:-2},N))
betti res coker transpose N

M
F=det M
L1={x_2,-x_2,x_3+x_2}
L2={x_0,-x_4,x_4}
L3={x_1,-x_1,x_5}
L4={x_0,x_2+x_3,x_5}
L5={2*x_1,x_4,x_2}
phi1=apply(L1,x->matrix{{x}})
phi2=herzog(phi1,rho,L2)
phi3=herzog(phi2,rho,L3)
phi4=herzog(phi3,rho,L4);
phi=herzog(phi4,rho,L5);
betti phi#0
PP=product(phi);
(PP_{0}^{0}**id_(target PP))==PP
PP_{0}^{0}==F


N=substitute(phi#0,matrix{{y_0*y_1,y_0*y_2,y_0*y_3,y_1*y_2,y_1*y_3,y_2*y_3}});
betti N
betti(N=map(E^81,E^{81:-2},N))
betti res coker transpose N
