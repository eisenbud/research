newPackage(
	"InverseSystems",
    	Version => "0.1", 
    	Date => "May 7, 2017",
    	Authors => {{Name => "David Eisenbud", 
		  Email => "de@msri.org"
		  }},
    	Headline => "equivariant Macaulay Inverse Systems",
    	DebuggingMode => true
    	)

export {"toDividedPowers",
        "fromDividedPowers",
	"fromDu",
	"toDu",
	"inverseSystem",
	--option names:
	"PowerBound",
	"DividedPowers"
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

--fromDu returns an ideal, not a matrix. Input is a matrix or a ring element
fromDu = method(Options=>{DividedPowers => false})						  
fromDu Matrix := o -> M -> (
    	  if numgens target M > 1 then error"input matrix has too many rows";
          if not isHomogeneous M then error"this version needs a homogeneous argument";
	  dtar :=  (degrees target matrix{{M}})_0_0;
	  R := ring M;
	  M' := R^{dtar}**M; -- set target degree to 0, just in case.
	  if o.DividedPowers === true then M' = toDividedPowers M';
	  
    	  dmax := first max degrees source M';
          g := product apply(generators R, v -> v^dmax);
          I1 := ideal contract(transpose M', matrix{{g}});
	  trim (ideal apply(numgens R, j->R_j^(dmax+1)) : I1)
	  )	  
fromDu RingElement := o -> f -> fromDu(matrix{{f}}, DividedPowers=> o.DividedPowers)

///
restart
loadPackage("InverseSystems", Reload =>true)
S = QQ[a,b]
f = matrix{{a,b^2}}
fromDu f
f = a^2*b
fromDu f
///

--toDu returns a matrix. input should be an ideal
toDu = method(Options=>{DividedPowers => false})
toDu(ZZ, Ideal) := o -> (d,f) -> (
         R := ring f;
         g := matrix {{product apply(generators R, v -> v^d)}};
         box := ideal apply(numgens R, j->R_j^(d+1));
         m := contract(
              mingens image (generators (box : f) % box),
              g);
	 m1 := map(target m, source m, (i,j) -> (degree m_j_i)_0*m_j_i);
	 if o.DividedPowers === false then m1 else fromDividedPowers m1
)
toDu(ZZ, Matrix) := o -> (d,M) -> toDu(d,ideal M, DividedPowers => o.DividedPowers)

powers := (R,d) -> matrix{apply(numgens R,j->R_j^d)}
containsDthPowers = I ->(
    R := ring I;
    D := 1;
    while powers(R,D)%I != 0 do D = D+1;
    D)

inverseSystem = method(Options => {DividedPowers => true, PowerBound => 0, Local => true})
inverseSystem Ideal := o-> I -> (
    d := o.PowerBound; -- this is potentially less than the regularity. Is this ok??

    if d===0 then(
     if 0==dim I and isHomogeneous I then d = containsDthPowers I -1
     else return "ideal not zero-dimensional; needs explicit option PowerBound.  
     Re-run as 
     inverseSystem(I, PowerBound => D)
     for appropriate D.");
     
    toDu(d,I,DividedPowers => o.DividedPowers)
    )
inverseSystem Matrix := o-> M -> (

    fromDu(M, DividedPowers => o.DividedPowers)
    )

TEST///
restart
uninstallPackage "InverseSystems"
loadPackage("InverseSystems", Reload => true)
setRandomSeed 0
kk = QQ
n = 3
S = kk[a,b,hvar]
I = ideal"a4,b5+b7"
J = ideal "a4,b5"
hI = homogenize(I, hvar)
inverseSystem (I, PowerBound => 4)
inverseSystem (I, PowerBound => 6)
inverseSystem (J
inverseSystem gens hI
inverseSystem gens J
///

beginDocumentation()


doc ///
Key
 InverseSystems
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
 I = fromDu m
 I = fromDu p
Inputs
 m:Matrix
 p:RingElement
Outputs
 I:Ideal
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
   betti res  fromDu f1
   betti res  fromDu f2
   betti res  fromDu(f2, DividedPowers =>true)
Caveat
 If any of the polynomials invoved has degree >= characteristic ring m,
 the option must be DividedPowers=>false.
SeeAlso
 fromDividedPowers
///

TEST///
--fromDividedPowers and toDividedPowers are inverse to one another
setRandomSeed 0
kk = QQ
n = 3
S = kk[a,b,c]
p = (a+b)^2
q = toDividedPowers p
assert(q == 2*a^2+2*a*b+2*b^2)
assert(p ==fromDividedPowers q)

P = (random(S^{0,1},S^{-2,-3}))
Q = fromDividedPowers toDividedPowers P
R = toDividedPowers fromDividedPowers P
assert(P==Q)
assert(P == R)
///

///TEST
--fromDu is equivariant on ideals
setRandomSeed 0
kk = QQ
n = 3
S = kk[a,b,c]
g = random(S^3, S^3)
testmap = map(S,S,(vars S)*g)
testmap' = map(S,S,(vars S)*(dual g)^-1)
f = random(S^1,S^{-2,-2,-3})
assert(testmap'  fromDu(f, DividedPowers =>true) == 
         fromDu(testmap f, DividedPowers => true))
assert(testmap' inverseSystem f == inverseSystem testmap f)
///

TEST///
--with or without divided powers,
-- applying fromDu toDu is the identity on ideals.
-- applying toDu fromDu is the identity on submodules of the dual.
setRandomSeed 0
S = QQ[a,b]
G = random(S^2,S^2)
GG = map(S,S,(vars S)*G)
GG' = map(S,S,(vars S)*transpose G^-1)
f = a^2
g = b^3
h = matrix{{f,g}}
assert(trim ideal GG h ==  fromDu toDu(4,GG h))
assert(trim ideal GG h ==  fromDu(
	                             toDu(4, GG h, 
					 DividedPowers=>true), 
				     DividedPowers =>true)
				 )
assert(ideal h == fromDu toDu(4, fromDu toDu(4,h)))
assert(ideal GG h == fromDu toDu(4, fromDu toDu(4,ideal GG h)))
assert(ideal GG h == fromDu(toDu(4, fromDu(toDu(4,ideal GG h),
		 DividedPowers=>true), DividedPowers => true)))
///

///
--the local, that is, inhomogeneous case:
S = QQ[a,b,c]
G = random(S^3,S^3)
GG = map(S,S,(vars S)*G)
M = matrix{{a^2+b^3}}
I1 = inverseSystem M
I2 = inverseSystem GG M
assert(hilbertSeries ideal leadTerm gens gb I1===hilbertSeries ideal leadTerm gens gb I2)

///

end--
restart
loadPackage("InverseSystems", Reload =>true)
uninstallPackage("InverseSystems")
installPackage("InverseSystems")
check "InverseSystems"
viewHelp InverseSystems
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
