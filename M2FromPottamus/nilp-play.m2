kk= ZZ/32003
R = kk[s,t,u,v,w,c]
M1 = matrix(R,{
     {0,w*u+w^2,w*v,c,0},
     {0,0,-w^2,-w*v-u*v,-c},
     {0,0,0,u^2,u*v},
     {0,0,0,0,-w*u-u^2},
     {0,0,0,0,0}}
     )
M2 = matrix(R,{
     {0,0,0,0,0},
     {1,0,0,0,0},
     {0,1,0,0,0},
     {0,0,1,0,0},
     {0,0,0,1,0}}
     )
M=s*M1+t*M2
F = res coker M
betti F
help substitute
N=substitute(M, {u=>1,w=>5,v=>7,c=>11})
F=res coker N
betti F

sparse