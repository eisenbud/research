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
///
restart
uninstallPackage "InverseSystems"
installPackage "InverseSystems"
///

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
    	  if numgens target M > 1 then error"Input matrix has too many rows.";
          if not isHomogeneous M then error"This version needs a homogeneous argument.";
--	  dtar :=  (degrees target matrix{{M}})_0_0;
	  dtar :=  (degrees target M)_0_0;	  
	  R := ring M;
	  M' := R^{dtar}**M; -- set target degree to 0, just in case.
	  if o.DividedPowers === true then M' = toDividedPowers M';
	  
    	  dmax := first max degrees source M';
          g := product apply(generators R, v -> v^dmax);
          I1 := ideal contract(transpose M', matrix{{g}});
	  trim (ideal apply(numgens R, j->R_j^(dmax+1)) : I1)
	  )	  
fromDu RingElement := o -> f -> fromDu(matrix{{f}}, DividedPowers=> o.DividedPowers)

lFromDu = method()
lFromDu Matrix := M ->(
    --M: 1-row, not necessarily homogenous, treated as local.
    R := ring M;
    n := numgens R;    
    dtar :=  (degrees target matrix{{M}})_0_0;
    M' := R^{dtar}**M; -- set target degree to 0, just in case.
    dmax := 2+first max degrees source M';
--    dmax := first max degrees source M';
    g := product apply(generators R, v -> v^dmax);
    J := ideal apply(generators R, v -> v^(1+dmax));
    M0 := contract(transpose M', matrix{{g}});
    X := symbol X;
    R1 := (coefficientRing R)[X_0..X_n, MonomialOrder => Eliminate 1];
    toR1 := map(R1,R,{X_1..X_n});
    M1 := toR1 M0;
    J1 := toR1 J;
    Mh := homogenize(M1, X_0);
    I1 := syz(Mh**R1/J1);
    error();
    leadTerm I1
    )
    
    
///
restart
loadPackage("InverseSystems", Reload =>true)
S = QQ[a,b]

f = matrix{{a,b^2+b^3}}
lFromDu f
leadTerm transpose Mh
I1
g = matrix"a,b2"
lFromDu g
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
 Replaces fromDual and toDual
Description
 Text
  The graded Hopf algebra dual of the symmetric algebra
  $S := k[x_1,\dots,x_n]$ is the divided power algebra
  $D$. The dual basis to the monomial basis of $S$
  is the basis consisting of monomials
  $x_1^{(m_1)} \dots x_n^{(m_n)}$ and multiplication
  (for example). In characteristic zero,
  $S$ and $D$ are isomorphic as algebras, with 
  isomorphism sending 
  $x_i^{a}$ to $a!x_i^{(a)}$, 
  and in general the multiplication in $D$ is defined
  by the same formulas as in characteristic 0 (after
  clearing denominators) so, for example,

  $x_1^{(1)}*x_1^{(1)} = 2*x_1^{(2)}$

  but in finite characteristic $D$ is not even
  a finitely
  generated algebra. We will be interested
  also in the local version, where we take power series
  in the divided powers; the result, which we denote
  by D', is the injective hull of the simple module
  $S/(x_1,\dots,x_n)$.  
  
  Since $D$ is the dual of $S$, it may be regarded as an
  $S$-module. The action of $S$ on $D'$ factors through
  the localization $S'$ of $S$ at $(x_1,\dots,x_n)$. 
  The (local) inverse system of an ideal in $S$
  or $S'$ is
  by definition the submodule of $D'$ it annihilates, and
  the inverse system of an $S'$-submodule of $D'$ is its
  annihilator in $S'$ (or in $S$). 
  
  In the 1880's these ideas were used by Max Noether, in the
  local version, as a substitute for primary decomposition in the 
  case of what he called multiple points in the plane. 
  F. S. Macaualay studied and greatly refined Noether's
  work, and for example identified the ideals I that are
  annihilators of cyclic submodules of $D'$ as the ideals
  such that one could do residuation in $S'/I$ -- 
  that is, $S'/I$ is Gorenstein.
  Though the global version
  has also been studied (see Emsalem [****]), we will only
  be concerned with the local version. 
  
  Any 
  finitely generated submodule of D' generated by finite
  polynomials is actually a submodule of D, and its dual
  will have only primary components contained in
  $(x_1,\dots,x_n)$ so the distinction
  will not be important for us on that side. 
  However, it is imporant
  to note that when taking the inverse system of an ideal,
  only the primary components contained in 
  $(x_1,\dots,x_n)$ play a role.
  
  Going from a submodule of D to an ideal of $S$: 
  
  Since Macaulay2 cannot deal directly with the S-modules 
  D or D', which are not finitely generated, we represent
  finitely generated submodules of D' by row matrices, of
  ordinary polynomials, in the default behavior
  of the script
  
  inverseSystem Matrix
  
  a monomial $x^a$ is taken to represent
  $a!x^(a) \in D'$, where,
  $a = (a_1,\dots,a_n)$ then $a! = a_1!*\dots*a_n!$.
  This means
  that the script should not be used in the default
  way unless the characteristic is greater than the highest
  degree to which a variable appears. 
  
  To make $x^a$ represent $x^(a)$,
  for example in small characteristics use
  
  inverseSystem(Matrix, DividedPowers=>false)
  
  (which was the default behavior of the old script
  "fromDual"). 

  The reason for the default choice is that the
  general linear group GL_n(k) acts on both S and D, and
  it is reasonable to expect that the operations
  defined by inverseSystem should be equivariant. This is
  the case for the default setting, but with
  DividedPowers=>false it is not the case:
  for example, the result of doing
  
  inverseSystem(matrix{{x_1^2}}, DividedPowers=>false)
  
  is a very different ideal (for example with a different
  betti table) than the result of 

  inverseSystem(matrix{{(x_1+x_2)^2}}, DividedPowers=>false)  
  
  Going from an ideal of S to a submodule of D:
  
  If $I$ is an ideal of $S$, homogeneous or not,
  we regard $I$ as an ideal of $S'$. If $S'/I$ is of
  finite length then
  
  M = inverseSystem I
  M1 = inverseSystem(I, DividedPowers => false)
  
  return a 1 x m matrix whose entries are
  the minimal generators of
  the annihilator of $I$ in $D'$. In the matrix $M$
  a term $x^a$
  is to be interpreted as 
  $a! x^(a)$, while in the matrix $M'$ it is interpreted
  as $x^(a)$. Of course the first computation is only
  valid if all the powers of variables appearing in the generators
  of $I$ are < char k.
  
  On the other hand, if $S/I$ is not of finite length, then the
  optional argument PowerBound is mandatory, and
 
  M = inverseSystem(I, PowerBound => d)
  M1 = inverseSystem(I, DividedPowers => false, PowerBound => d)

  will compute as above but with results valid only up to degree d.
  
  To make these computations it is necessary to represent some sufficiently
  large finitely generated S-submodule of $D'$ (this will automatically be
  an $S'$-submodule. To do this we use the map of modules
  D'-> S/(x_1^d,\dots, x_n^d) sending $x^{(a)}$ to 
  contract(x^a, product(n, j-> x_i^{d-1})), defined only when the variables
  in $x^{(a)}$ appear only with powers < d.
  
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
    fromDividedPowers
   Headline 
    Translates from divided power basis to monomial basis
   Usage
   Inputs
   Outputs
   Description
    Text
    Example
   SeeAlso
    toDividedPowers
///
doc ///
   Key
    toDividedPowers
   Headline
    translates from monomial basis to divided power basis
   Usage
   Inputs
   Outputs
   Description
    Text
    Example
   SeeAlso
    fromDividedPowers
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
