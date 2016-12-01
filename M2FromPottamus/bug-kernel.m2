
kk=ZZ/101
R=kk[x,y,z]
i=ideal"xyz,x3y,y2z2"
S=kk[x,y,z,u,v,w,Degrees=>{3:{1,0},{3,1},{4,1},{4,1}}]
T=kk[x,y,z,t,Degrees=>{3:{1,0},{0,1}}]
j=gens (t*substitute(i,T))
degrees j
f=map(T,S,(vars T)_{0..2}|j)
kernel f
--bombs!