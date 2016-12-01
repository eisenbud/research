random(Sequence, Ring) := o-> (degs, R) ->(
     for d in deepSplice degs list random(d,R))

degreeOfBigraded = M ->(
     --M must be a 2-dimensional bigraded module over a polynomial ring
     --with gens in degrees {1,0} and {0,1} (that is, M represents a sheaf
     --supported on a zero-dimensional scheme in P^m x P^n).
     if M==0 then return 0;
     S:= ring M;
     r1 := regularity(M, Weights=>{1,0})+#select(gens S, v->degree v == {1,0});
     r2 := regularity(M, Weights=>{0,1})+#select(gens S, v->degree v == {0,1});
     hilbertFunction({r1,r2}, M))
///
S = kk[a,b,c,d, Degrees=>{2:{1,0},2:{0,1}}]
i = intersect(ideal"ad-bc,ab", (ideal(a,b))^3)
i = ideal"ad-bc,ab"

assert( degreeOfBigraded (S^1/ideal"a3,c2")==6)
assert( degreeOfBigraded (S^1/i)==2)
M= S^1/i
     r1 = regularity(M, Weights=>{1,0})
     r2 := regularity(M, Weights=>{0,1})
     hilbertFunction({r1,r2}, M))

///

segreClass = method(Options=>true);
segreClass Ring := List => {BigradeBase=>false} >> opts -> R1 -> (
-- R is a bigraded tower ring R = S[e_0..e_m], with gens e_i in bidegrees (1,di) (di pos or neg ints)
-- S is a bigraded polynomial ring with generators in degrees (0,1)
-- the script computes the Segre classes of the cone represented by Bi-Proj R over Proj S = P^n.
-- If q: C -> Pn is the structure map of the cone, with relative dimension rD,
-- then the Segre classes are
-- s^i(C) = q_*(c_1(OO_C(1))^(i+rD)\cap [C]).

-- The idea is to first twist the cone by a sufficiently positive line bundle so O(1) is generated
-- by global sections, and then to push forward intersections of more and more general sections.
-- The pushforward of a given class is computed by restricting to a general plane section of the
-- image variety, and then computing the dimension of the module of 
-- global sections of the sheaf represented by the 1-dimensional
-- module that is the pushforward of the structure sheaf of the fiber.

--The Segre classses of the cone and of its twist are related by a simple formula
--because OO_{C(L)}(1) = OO_C(1)\otimes L, and thus 
--q_*(c_1(OO_{C(L)}(1))^i+rD) = sum_j(c_1(L)^j q_*(c_1(OO_C(1))^(i+rD-j)).
--This is an invertible transformation that is undone by the matrix "inv" at the end of this script.

-- CAVEATS: We assume that "random" is "general". To fix that, one should put in tests
-- and either choose again if the choices are bad or else return an error.
  --get rid of components supported over the origin only.
  R := R1/saturate(ideal 0_R1, ideal vars R1);
  --assume temporarily that the gens of R are in degree {1,0} and the coeff ring has degrees {0,1}
  if opts.BigradeBase == true then R =  correctReesGrading R1;
  dimR := dim R;
  --flatten the ring, and get rid of components supported at the origin if any.
  Rflat := first flattenRing R; 
  -- we'll make our computations here
  
  --construct some useful ideals and lists of random elements:  
  fibervars=ideal select(gens Rflat, v-> degree v == {1,0});
  basevars=ideal select(gens Rflat, v-> degree v == {0,1});
  RflatList := random(dimR-2:{1,0}, Rflat);
  Slist := random(dimSbar:{0,1}, S);

  S := coefficientRing R;
  dimS := dim S;
  dimSbar := dim ker map(R,S);
  --we want the relative dimension of the components that cover the largest part of the base:
--  rD := dimR - dimSbar -1; -- relative  dimension of the cone and its image
  rD := -1+dim (Rflat/sub(ideal(Slist_(0..dimSbar-1)), Rflat));
-- Form a list of random global sections of O(1) on the twisted cone, and random linear forms on the base
  RflatList := random(dimR-2:{1,0}, Rflat);
  Slist := random(dimSbar:{0,1}, S);
-- and compute the ideals they generate, saturated   
  LRflat := apply(rD..dimR-2, i -> if i==0 then 
         saturate(saturate(ideal 0_Rflat,basevars),fibervars) 
	 else
         saturate(saturate(ideal RflatList_{0..i-1}, basevars),fibervars));

-- Form the images in P^n
-- the following step is probably not necessary
  LS := apply(LRflat, i-> ker map(Rflat/i, S));

-- Reduce each ideal in LS to dimension 1
  LSbar := apply(LS, i->(
	  dimi := dim i;
	  if dimi<1 then I1 = ideal(1_S) 
	  else if dimi == 1 then i
	  else I1 = i+ideal(Slist_{0..(dimi-2)})
	  ));

-- and take the fiber over it of the variety defined by the i-th ideal of LRflat
  LRmods := apply(#LSbar, i -> Rflat^1/(LRflat#i+sub(LSbar#i, Rflat)));

--lift back to a poly ring to compute regularities
  psi:= gens ideal Rflat;
  T := ring psi;
  Tmods := apply(LRmods, M->(
	  Phi:=sub(presentation M, T);
	  G:=target Phi;
	  coker(Phi|G**psi)));

--Calculate the Segre classes of the twisted cone
  twistedSegre := apply(Tmods, M->(degreeOfBigraded M));
--error();
-- Undo the effect of the twist (if any)
d=0;--temporary assumption
  if d===0 then ans1 := twistedSegre else(
  inv := inverse map(QQ^dimSbar, QQ^dimSbar, (i,j)->((binomial(rD+i, rD+j))*d^(i-j)));
  ans1 = flatten entries(inv*(transpose matrix{twistedSegre})));

-- Pad with leading zeros if S -> R is not an inclusion
  toList(dimS-#ans1:0)|ans1
)

correctReesGrading = method();
correctReesGrading QuotientRing :=
correctReesGrading PolynomialRing :=
correctReesGrading Ring := Ring => (R) -> (
     -- R is a Rees algebra of an ideal of its coefficient ring.
     -- corrects the grading of R to be input into segreClass().
     S := coefficientRing R;
     if (degreeLength S =!= 1) then error "Degree length of the coefficient ring should be +1.";
     degS1 := (gens S / degree) / (d -> {0,d#0});
     S1 := newRing(S, Degrees => degS1);
     gensR := gens R;
     R1Ambient := S1[gensR, Degrees => (gensR / degree), Join => false];
     R1Ambient/sub(ideal R, R1Ambient)
)

end

restart
load "segreClasses.m2"

--example 0: Proj of the symmetric algebra of the trivial vector bundle
S = kk[x_0..x_2, Degrees => {3:{0,1}}];
R = S[e_0, e_1, Degrees => {2:{1,0}}, Join => false]
s0=segreClass R -- inverse of the Chern class of OO_{P2}++OO_{P2}

--example 0A: Proj of the symmetric alg of the vector bundle OO_{P1}(1)
--represented by its truncation generated in deg 0
S = kk[x_0..x_1]

for d from 0 to 3 do(
M=truncate(0,S^{d});
R = symmetricAlgebra M;
describe R;
print segreClass(R, BigradeBase=>true); -- inverse of the Chern class of OO_{P2}(2)++OO_{P2}
)

restart
load "segreClasses.m2"

S = kk[a,b]
M=truncate(0,S^{2})
R = symmetricAlgebra M
describe R
dim R
s0A=segreClass(R, BigradeBase=>true) -- inverse of the Chern class of OO_{P2}(2)++OO_{P2}


Rflat = first flattenRing R
gens Rflat/degree






















     
--example 1: Proj of the symmetric alg of the vector bundle OO_{P2}(-2)++OO_{P2}
S = kk[x_0..x_2, Degrees => {3:{0,1}}];
R = S[e_0, e_1, Degrees => {{1,0}, {1,2}}, Join => false]
s1=segreClass R -- inverse of the Chern class of OO_{P2}(2)++OO_{P2}

--example 1A: Proj of the symmetric alg of the vector bundle OO_{P2}(-2)++OO_{P2}
S = kk[x_0..x_2]
M=truncate(0,S^1++S^{2})
M=truncate(0,S^{2})
R = symmetricAlgebra M
s1=segreClass(R, BigradeBase=>true) -- inverse of the Chern class of OO_{P2}(2)++OO_{P2}



Rflat = first flattenRing(R)
gens Rflat/degree
ideal Rflat
pvars = (vars Rflat)_{0..6}
xvars = (vars Rflat)_{7..9}
T = ring ideal Rflat
fp=ideal((vars Rflat)*random(source vars Rflat, Rflat^{{-1,0}}))
fx=ideal((vars Rflat)*random(source vars Rflat, Rflat^{2:{0,-1}}))

degreeOfBigraded(T^1/(ideal Rflat+sub(fp+fx, T)))

--example 2: Proj of the symmetric alg of the tangent bundle of P2
S = kk[x_0..x_2, Degrees => {3:{0,1}}];
R1 = S[e_0..e_2, Degrees => {3:{1,-1}}, Join => false]
R=R1/ideal(sum(3,i->x_i*e_i))
s2=segreClass R -- inverse of the Chern class of the cotangent bundle

--example 3: The blowup of a point in P2
S = kk[x_0..x_2, Degrees => {3:{0,1}}];
R1 = S[e_0..e_1, Degrees => {2:{1,1}}, Join => false]
J = minors(2,matrix{
	  {x_0,x_1},
	  {e_0,e_1}})
R=R1/J
s3=segreClass R 

--example 3A: The blowup of a point in P2

S = kk[x_0..x_2]
R = reesAlgebra(ideal(x_0,x_1), x_0)
s3a=segreClass (R, BigradeBase =>true)

--example 4: The blowup of a point in a P2 regarded as a plane in P3
S = kk[x_0..x_3, Degrees => {4:{0,1}}];
R1 = S[e_0..e_1, Degrees => {2:{1,1}}, Join => false]
J = minors(2,matrix{
	  {x_0,x_1},
	  {e_0,e_1}})
R=R1/(J+ideal(sub(x_3,R1)))
s4=segreClass R 


assert(s0=={1,0,0})
assert(s1=={1,-2,4})
assert(s2=={1,3,3})
assert(s3=={1,0,-1})
assert(s3a==s3)
assert(s4=={0,1,0,-1})


--Goal: figure out what the Segre classes mean for Rees algebras.
restart
load "segreClasses.m2"
S = kk[x_0..x_2, Degrees => {3:{0,1}}];
R=S[y,Degrees=>{{1,0}}, Join=>false]
R2=S[y,z,Degrees=>{2:{1,0}}, Join=>false]/ideal(y^2)
segreClass R
segreClass R2



--find the degree of a zero-scheme in P^n x P^m



