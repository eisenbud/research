R=kk[s,t]
S=kk[x_1,x_2,x_3,x_4]
f=map(R,S,matrix{{s+t, t^2+2*s*t,t^3+3*s*t^2,t^4+4*s*t^3}})
i= kernel f
M=S^1/i
j=presentation M
transpose j
codim i
