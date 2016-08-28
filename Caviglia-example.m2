--Caviglia's old examples of regularity quadratic in the degree of the 4 generators in 6 vars.

kk = ZZ/101
S = kk[a,b,x,y,u,v]
Cav = n-> I = ideal(u^n,v^n, u*x^(n-1)+v*y^(n-1)+u*v*(x^(n-1)*a+y^(n-1)*b))
betti res Cav 3
for n from 2 to 10 do print ((n^2-1) == regularity Cav n)
