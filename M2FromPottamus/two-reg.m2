kk=ZZ/32003
n=4


example=(n,k)->(
     S=kk[x_1..x_((2+k)*n)];
     M=genericMatrix(S,x_1,n, 2+k);
     cols = ideal genericMatrix(S,x_1,n,k);     
     I=ideal mingens (minors(2,M)+(cols)^2);
time regularity module I)
example(4,2)
regularity
