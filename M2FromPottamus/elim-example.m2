kk=ZZ/32003
S=kk[w,x,y,z]
R=kk[s,t]
param=map(R,S,{s,s^2,s^3+s^5})
kernel param

par2=map(R^1,R^{-3,-3,-3,-3},{{t^3,s*t^2,s^2*t,s^3}})
isHomogeneous par2
param2=map(R,S,par2)
kernel param2
