restart
kk=ZZ/101
R=kk[s,t,u,v,a,Degrees=>{4:1,0}]
I=ideal(u^3,v^3,s^2*u+t^2*v+a*s^3)
betti res I
I0=ideal(gens I%ideal a)
betti res I0
cI=primaryDecomposition(I0)



A=matrix{{x_0,t*x_1,x_2,x_3},{x_1,x_2,t*x_3,x_4}}
I=minors(2,A)
betti(J=saturate(I,t))
transpose gens J
betti res J
Jt=saturate(J+ideal t)
betti res Jt
