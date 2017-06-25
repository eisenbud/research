restart
--Rational normal quartic
R = ZZ/101[a..e]
s = 5
m = matrix"a,b,c,d;b,c,d,e"
I = minors(2,m);
ff = ideal ((gens I) * random(source gens I, R^{5:-3}));
K = ff:I;
codim K -- s-residual intersection
betti res K 
M = prune((module I)/module(ff));
--time (S2M = symmetricPower(2,M))
---too slow to wait!



--Better:
symmPower = (d,M) ->(
R := ring M;
g := presentation M;
r := numgens target g;
X := symbol X;
kk := ultimate(coefficientRing, R);
R' := kk[X_1..X_r];
Y2 := basis(d-1,R');
Y1 := basis(1,R');
mult := (Y1**Y2)//(basis(d,R'));
L := flatten entries gens ((ideal vars R')^d);
L1 := apply(L, i->flatten exponents i);
degs := apply(L1,i->sum(#i,j->i_j*(degrees (target g))_j));
m := map(R^(-degs),,matrix((sub(mult, R))*(g**symmetricPower(d-1,target g))));
coker m
)

time symmPower(2,M);
     -- used 0.0241902 seconds
