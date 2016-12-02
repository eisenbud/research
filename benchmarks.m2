m=5;
n=4;
S = ZZ/101[x_0..x_(m*n-1)]
M = genericMatrix(S,x_0,m,n)
I = minors(2,M)
time betti res I
