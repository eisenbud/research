n:=4;
P:= PolynomialRing(GF(32003), 2*n^2, "grevlex");P;
M:=Matrix([[P.i : i in [n*j+1..n*(j+1)]]: j in [0..n-1]]);M;
N:=Matrix([[P.i : i in [n^2+n*j+1..n^2+n*(j+1)]]: j in [0..n-1]]);N;
Q:=M*N-N*M;
I:=Ideal([Q[i][j] : i in [1..n], j in [1..n]]);
time G:=GroebnerBasis(I);
#G;
Sort([Degree(G[i]): i in [1..#G]]);
