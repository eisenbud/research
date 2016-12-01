restart
m=6
r=3
n=4
i=2
S=kk[x_1..x_((m+n)*r)]
vars S
phi=genericMatrix(S,x_1,n,r)*genericMatrix(S,x_(r*n+1),r,m)
codim minors(i,phi)
