--How big is the family of Gorenstein
--"almost linear" ideals gen in deg d in n vars?
-- A subfamily is obtained by embedding the twisted
--module as an ideal gen in degree d in kk[x_1,..x_n]/(x_2,..,x_n)^d
--Answer: binomial(d+n-3, n-2)^2; As there are m=binomial(d+n-3,n-2)
--generators, this suggests GL(m)...

n=4
d=4
S=kk[x_1..x_n]
ind=(ideal(x_1..x_(n-1)))^d
--the following is omega_(S/ind)(2d-2), which is generated in deg d
omega2=Ext^(n-1)(S^1/ind, S^{-n-(2*d-2)})
betti omega2
betti prune truncate(d, Hom(omega2,S^1/ind))
xc