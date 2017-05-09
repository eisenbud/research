newPackage(
	"DividedPowers",
    	Version => "0.1", 
    	Date => "May 7, 2017",
    	Authors => {{Name => "David Eisenbud", 
		  Email => "de@msri.org"
		  }},
    	Headline => "to and from Divided Power basis",
    	DebuggingMode => true
    	)

export {"toDividedPowers",
        "fromDividedPowers",
	"fromDu",
	"DividedPower" -- change to DividedPowers 
	}


toDividedPowers = method()
toDividedPowers RingElement := p -> (
    --the following routine takes a polynomial and writes in in the divided power basis,
    --where a^(n) is represented as a^n.
    S := ring p;
    sub0 := map(S,S,0_S*vars S);
    (monoms, coeffs) := coefficients p;
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
    (monoms, coeffs) := coefficients p;
    D := sub0 diff(monoms, transpose monoms);
    (flatten entries (monoms*(inverse D)*coeffs))_0
)
fromDividedPowers Matrix := M -> (
    map(target M, source M, (i,j) -> fromDividedPowers (M_j_i))
)

fromDu = method(Options=>{DividedPower => false})
fromDu Matrix := o -> M -> if o.DividedPower === false then fromDual M else 
                                                  fromDual toDividedPowers M
fromDu RingElement := o -> f -> fromDu(matrix{{f}}, DividedPower=> o.DividedPower)

toDu = method(Options=>{DividedPower => false})
toDu(ZZ, Matrix) := o -> (d,f) -> (
         R := ring f;
         g := product apply(generators R, v -> v^d);
         box := matrix table (1, numgens R, (i,j) -> R_j^(d+1));
	 if o.DividedPower === false then return
         contract(
              transpose mingens image (generators (image box : image f) % box),
              matrix{{g}})
	 


beginDocumentation()


doc ///
Key
 DividedPowers
Headline
 Translate from/to divided power basis
Description
 Text
  The Hopf algebra dual of the symmetric algebra
  $k[a_1,\dots,a_n]$ is the divided power algebra, whose basis consists of monomials
  a_1^{(m_1)} \dots a_n^{(m_n)}. In characteristic zero these algebras are
  isomorphic, with the isomorphism sending 
  $x_i^{a_i}$ to $a_i!  x_i^{(a_i)}$.
 Example
  setRandomSeed 0
  kk = QQ
  S = kk[a,b,c]
  map(S,S,0_S*vars S)
  p = (a+b)^2
  q = toDividedPowers p
  p' = fromDividedPowers q
  p'==p
Caveat
 The translations used involve multiplying or dividing by scalars; if the polynoimials
 involved have maximum degree n, then n! must be invertible for the translation to make sense.
SeeAlso
 fromDividedPowers
 toDividedPowers
///


doc ///
Key 
 fromDu
 (fromDu, Matrix)
 (fromDu, RingElement)
Headline
 fromDual with optional divided power translation
Usage
 M = fromDu m
 M = fromDu p
Inputs
 m:Matrix
 p:RingElement
Outputs
 M:Matrix
Description
  Text
    transforming f to g(f) in the polynomial basis and then applying 
    fromDual toDividedPowers g(f)
    gives an ideal that is equivalent to 
    fromdual toDividedPowers f: more precisely,
    (transpose inverse g) fromDual toDividedPowers g(f)
    generates the same ideal as 
    fromDual toDividedPowers f
  Example
   S = QQ[a,b,c]
   f1 = a^2
   f2 = (a+b)^2
   betti res coker fromDu f1
   betti res coker fromDu f2
   betti res coker fromDu(f2, DividedPower =>true)
Caveat
 If any of the polynomials invoved has degree >= characteristic ring m,
 the option must be DividedPower=>false.
SeeAlso
 fromDividedPowers
///

TEST///
setRandomSeed 0
kk = QQ
n = 3
S = kk[a,b,c]
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

g = random(S^3, S^3)
testmap = map(S,S,(vars S)*g)
testmap' = map(S,S,(vars S)*(dual g)^-1)
f = random(S^1,S^{-2,-2,-3})
I1 = fromDual toDividedPowers testmap f
I2 = testmap' fromDual toDividedPowers f
assert(trim ideal I1==trim ideal I2)
///

end--
restart
loadPackage("DividedPowers", Reload =>true)
uninstallPackage("DividedPowers")
installPackage("DividedPowers")
check "DividedPowers"
viewHelp DividedPowers
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



