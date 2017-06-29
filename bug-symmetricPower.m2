symmPower0 = (d,M) ->(
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

--Dan's code
symmPower = (d,M) ->(
  R := ring M;
  g := presentation M;
  r := numgens target g;
  kk := ultimate(coefficientRing, R);
  X := symbol X;
  R' := kk[X_1..X_r];
  coker (
       (sub((basis(1,R')**basis(d-1,R'))//(basis(d,R')), R))
       *
       (g**symmetricPower(d-1,target g))))

TEST///
restart
load "bug-symmetricPower.m2"
--Rational normal quartic
R = ZZ/101[a..e]
s = 5
m = matrix"a,b,c,d;b,c,d,e"
I = minors(2,m);
ff = ideal ((gens I) * random(source gens I, R^{5:-3}));
M = prune((module I)/module(ff));
--time (S2M = symmetricPower(2,M))
---too slow to wait!

time P0 = symmPower0(5,M); -- fast
time P = symmPower(5,M); -- slightly faster
betti presentation P0
betti presentation P
betti symmetricPower(5, target presentation M)

R = ZZ/101[a,b,c][d,e,f, Degrees => {{1,0},{1,2},{3,1}}]
(gens R)/degree
(S,phi) = flattenRing R
(gens S)/degree
FR = R^{{1,2,3},{3,2,1}}
FS = phi FR
MR = coker (FR**koszul(2,vars R))
MS = coker (FS**koszul(2,vars S))
time symmPower(5,MR);      -- used 0.107596 seconds
time symmPower0(5,MR);      --  used 0.123574 seconds

--time symmPower(5,MS);       -- used 59.6126 seconds!
--time symmPower0(5,MS);      -- used 67.6282 seconds
--why is the version with MS soooo much slower than the version with MR?

time symmPower(4,MS);       -- used 3.56396 seconds 
time symmPower0(4,MS);      -- used 3.51283 seconds



Nold = symmetricPower(1,MR)
N0 = symmPower0(1,MR)
N = symmPower(1,MR)
betti presentation Nold
betti presentation N0
betti presentation N


symmetricPower(1,MS)
symmPower0(1,MS)
symmPower(1,MS)

///
end--
restart
load "bug-symmetricPower.m2"
