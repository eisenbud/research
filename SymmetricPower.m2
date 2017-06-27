
--a replacement for the method (symmetricPower, Module), which
--was very slow on moderate examples. 
--Now completely independent of the old code and very much faster.

symmPower = (d,M) ->(
R := ring M;
g := presentation M;
r := numgens target g;
X := symbol X;
kk := ultimate(coefficientRing, R);
--the following block of code produces the 
--lists of lists of integers L1 necessary
--to set the degrees of the target of the 
--symmetric power map correctly
R' := kk[X_1..X_r];
Y2 := basis(d-1,R');
Y1 := basis(1,R');
mult := (Y1**Y2)//(basis(d,R'));
L := flatten entries gens ((ideal vars R')^d);
L1 := apply(L, i->flatten exponents i);
K := flatten entries gens ((ideal vars R')^(d-1));
K1 := apply(K, i->flatten exponents i);
--Now set the degrees:
degsTar := apply(L1,i->sum(#i,j->i_j*(degrees (target g))_j));
degsLower := apply(K1,i->sum(#i,j->i_j*(degrees (target g))_j));
--
promo := map(R,R');
m1 := map(R^(-degsTar),,promo mult);
m2 := g**R^(-degsLower);
--check that all is well:
assert(source m1 == target m2);
coker(m1*m2)
)

TEST///
restart
load "SymmetricPower.m2"
S = ZZ/101[a,b][c,d, Degrees =>{{1,2},{3,1}}]
F = S^{{1,1,1},{2,2,3}}
assert(degrees symmPower(2, F) == {{-2, -2, -2}, {-3, -3, -4}, {-4, -4, -6}})

M1 = coker matrix {{c, d}, {c, d}}
toString symmPower(2, M1)
assert(symmPower(2, M1) == cokernel matrix {{c, 0, d, 0}, {c, c, d, d}, {0, c, 0, d}})

M2 = coker map(S^{{1,2,3}, {3,1,2}},S^1, matrix"ca3;b2d")
assert isHomogeneous symmPower(3, M2)
assert(symmPower(3,M2) == symmetricPower(3, M2))
///

end--

--original motivation:
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

time symmPower(2,M);
     -- used 0.0241902 seconds

--a version dependent on the old code:
symmPower = (d,M) ->(
R := ring M;
g := presentation M;
r := numgens target g;
X := symbol X;
kk := ultimate(coefficientRing, R);
--the following block of code only produces the list of lists of integers L1 necessary
--to set the degrees of the target of the symmetric power map correctly
R' := kk[X_1..X_r];
Y2 := basis(d-1,R');
Y1 := basis(1,R');
mult := (Y1**Y2)//(basis(d,R'));
L := flatten entries gens ((ideal vars R')^d);
L1 := apply(L, i->flatten exponents i);
--Now set the degrees:
degs := apply(L1,i->sum(#i,j->i_j*(degrees (target g))_j));
--
promo := map(R,R');
m1 := map(R^(-degs),,matrix promo mult);
--trust the old symmetricPower code to produce 
--the symmetric power of a free module
m2 := (g**symmetricPower(d-1,target g));	
--check that all is well:
assert(source m1 == target m2);
coker(m1*m2)
)
