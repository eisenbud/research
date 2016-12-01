k=3
g=2*k+1;
kk=ZZ/101



R=kk[x_1..x_g,y_1..y_g]
m=matrix table (2,g,(i,j)->R_(i*g+j))
i=minors(2,m)
ires=res i
v=map(ires_k,R^{-(k+1)},matrix table(rank ires_k,1,(i,j)->
	             if i==49 then 1_R else 0_R))


syzygyScheme(ires,3,v)

code syzygyScheme

-----------------------
kk=ZZ/101
R=kk[s,t_1..t_3,r,u,v]
S=kk[x_{0,0}..x_{1,3}]
f=map(R,S,matrix{{2*u^4*v,u^3*(t_1*s+s*v),u^2*(t_2*s^2+v*s^2),
	       u*(t_3+v)*s^3,u^3*(r+v)*s,u^2*(t_1+r)*s^2,
	  u*(t_2+r)*s^3,(t_3+r)*s^4}})
i=kernel f
betti res i
codim i
degree i
j=ideal(x_{1,0}-x_{0,1}, x_{1,1}-x_{0,2}, x_{1,2}-x_{0,3})
