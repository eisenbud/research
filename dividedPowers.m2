-- make "fromDual" equivariant for the action of GLn
--
--transforming f to g(f) in the polynomial basis and then applying 
--fromDual toDividedPowers g(f)
--gives an ideal that is equivalent to 
--fromdual toDividedPowers f
--in fact 
--(transpose inverse g) fromDual toDividedPowers g(f)
--generates the same ideal as 
--fromDual toDividedPowers f

toDividedPowers = method()
toDividedPowers RingElement := p -> (
    --the following routine takes a polynomial and writes in in the divided power basis,
    --where a^(n) is represented as a^n.
    S := ring p;
    sub0 := map(S,S,0_S*vars S);
    (monoms, coeffs) = coefficients p;
    D := sub0 diff(monoms, transpose monoms);
    (flatten entries (monoms*D*coeffs))_0
)
toDividedPowers Matrix := M -> (
    map(target M, source M, (i,j) -> toDividedPowers (M_j_i))
)

fromDividedPowers = method()
fromDividedPowers RingElement := p -> (
    --the following routine takes a polynomial written in the divided power basis,
    --where a^(n) is represented as a^n,
    --and changes it to a polynomial written in the monomial basis.
    S := ring p;
    sub0 := map(S,S,0_S*vars S);
    (monoms, coeffs) = coefficients p;
    D := sub0 diff(monoms, transpose monoms);
    (flatten entries (monoms*(inverse D)*coeffs))_0
)
fromDividedPowers Matrix := M -> (
    map(target M, source M, (i,j) -> fromDividedPowers (M_j_i))
)


TEST///
setRandomSeed 0
kk = QQ
n = 3
S = kk[vars(0..2)]
map(S,S,0_S*vars S)
p = (a+b)^2
q = toDividedPowers p
assert(q == 2*a^2+2*a*b+2*b^2)
assert(p ==fromDividedPowers q)

P = (random(S^{0,1},S^{-2,-3}))
Q = fromDividedPowers toDividedPowers P
R = toDividedPowers fromDividedPowers P
assert(P==Q)
assert(P == R)

--test of equivariance: 
--transforming f to g(f) in the polynomial basis and then applying 
--fromDual toDividedPowers g(f)
--gives an ideal that is equivalent to 
--fromdual toDividedPowers f
--in fact 
--(transpose inverse g) fromDual toDividedPowers g(f)
--generates the same ideal as 
--fromDual toDividedPowers f
g = random(S^3, S^3)
testmap = map(S,S,(vars S)*g)
testmap' = map(S,S,(vars S)*(dual g)^-1)
f = random(S^1,S^{-2,-2,-3})
I1 = fromDual toDividedPowers testmap f
I2 = testmap' fromDual toDividedPowers f
assert(trim ideal I1==trim ideal I2)
///
end

restart
load "dividedPowers.m2"
kk = ZZ/101
S = kk[a..d]

--some codim 4 Gorenstein rings with quartic socles

f = matrix"a2b2+c2d2" -- gives 1,4,6,4,1
f = matrix"a2b2+b2c2+c2d2" --gives 1,4,7,4,1
f = matrix"a2b2+b2c2+c2d2+c2a2" -- gives 1,4,8,4,1
f = matrix"a2b2+b2c2+c2d2+c2a2+a2d2" --gives 1,4,8,4,1
f = matrix"a2b2+b2c2+c2d2+c2a2+a2d2+b2d2+b4" --gives 1,4,9,4,1
f = matrix"a2b2+b2c2+c2d2+c2a2+a2d2+b2d2" --gives 1,4,10,4,1

g = random(S^(numgens S), S^(numgens S));
autoS = map(S,S,(vars S)*g);
autoS' = map(S,S,(vars S)*dual g);
I = ideal fromDual toDividedPowers autoS' f;
J = ideal autoS^-1 fromDual toDividedPowers f;
assert(I==J)



