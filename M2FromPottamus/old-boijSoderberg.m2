--Testing the Boij-Soderberg Conjecture.

--charFreePure
--TwoEquivariantPure
--pureHilb
--pureBetti
--pureBettiDiagram
--bettiH
--rkSchur
--Weyman
--lowestDegrees
--highestDegrees
--projectiveDimension
--isStrictlyIncreasing
--decompose1
--decomposeAll
--mat2betti
--testSocle
--testGenerators
--pureHilb
--Betti2Hilb
--hashTable2Hilb
--bin  
-- binomial coeff
--hp  -- Hilbert poly as fcn of betti numbers
--bettiNumbers -- makes a matrix from pureBetti

-----Facet Equation routines
--rangeOK
--bettiMatrix
--nextLower
--nestUpper
--lowerRange
--upperRange
--rangeMatrices
--peskineSzpiro
--numericalComplex
--flipEquation
--middleComplex
--nextPure
--twoRowPureComplex
--twoRowFacet
--threeRowFacet
--supportingEquation
--facetEquation(List,ZZ,ZZ,ZZ):=(d,i,lowestDegree, highestDegree)

--dotProduct
--supportFunctional

--randomDegreeSequence(n, maxdegshift)
--betti2matrix

--Bott

--Most important routines:

--charFreePure
--gives beta_0 for the pure complex described in Eisenbud-Schreyer

--TwoEquivariantPure
--gives beta_0 for the pure complex described in Eisenbud-Weyman-Floeystad for two modules

--matToBetti takes a matrix of integers and produces a "betti tally"
-- (suitable input to the builtin function "betti") which produces the
--corresponding betti table.

--decomposeAll 
--input: a BettiTally or a similar hash table
--output: The routine prints the Boij-Soderberg summands.
--prints "not in convex hull" if the given BettiTally is not in the convex
--hull of the allowable pure betti diagrams. Prints an error message
--if the decomposition fails. Returns a list of the components as a list of pairs,
--each a rational coefficient followed by a hash table representing a pure betti diagram,
--if it succeeds.
--NEW: this version also works for non Cohen-Macaulay modules.

--testSocle
--takes a degree sequence and produces the generic "level" module with same
--socle and generator type of a module that would have the minimal possible
--pure resolution with that degree sequence. (this module does NOT in general
--have a pure resolution!)

--testGenerators 
--does the same thing, but with random choices of the right number of generators in the right
--degree.

--pureHilb
--takes list of degrees, computes the hilbert function of the module with 
--corresponding pure resolution

--rkSchur
--rank of a Schur functor on a module
--input: a non-neg integer n and a non-increasing sequence of non-neg integers L
--output: the rank of the representation S_L(C^n). Here (11111) represents an exterior power, (k) a symmetrci power.

--Bott(List, ZZ)
     --given a weakly decreasing list of integers L of length n and an integer u,
     --uses Bott's algorithm to compute the cohomology of the vector bundle 
     -- E=O(-u) \tensor S_L(Q), on P^n = PP(V)
     --where Q is the tautological rank n quotient bundle in the sequence 
     --   0--> O(-1) --> O^(n+1) --> Q -->0
     --and S_L(Q) is the Schur functor with the convention S_(d,0..0) = Sym_d, S_(1,1,1) = \wedge^3 etc.
     --returns either 0, if all cohomology is zero,
     -- or a list of three elements: A weakly decreasing list of n+1 integers M;
     -- a number i such that H^i(E)=S_M(V); and 
     -- the rank of this module.
--Bott(List,ZZ,ZZ)
     --produces the betti diagram of the tate resolution of the sheaf S_L(Q),
     --between the column whose index is "low" and the column whose index is "high"

-----------------------------
charFreePure=L -> (product(1..#L-1, i->binomial(L_i-L_0-1, L_i-L_(i-1)-1)))
--gives beta_0 for the pure complex described in Eisenbud-Schreyer


TwoEquivariantPure=L->(
--gives beta_0 for the pure complex described in Eisenbud-Weyman-Floeystad for two modules
   n:=#L-1;
   T={};
     E=for i from 1 to #L-1 list (L_i-L_(i-1));
     for i from 1 to #E do
     for j from 1 to E_(n-i)-1 do (T= T| {n-i});
     T=T |  {0};
     rkSchur(#T, toSequence T)
     )

///
restart
load "BoijSoderberg.m2"
L=(1,2,3)
L=(0,1,3,4)
L=(0,11,13,24)
TwoEquivariantPure L
test=L->(G= (Weyman L, charFreePure L, TwoEquivariantPure L);
     print "" ;
     print(gcd G, G))
L=(0,11,13,24)
L=(0,2,7,10)
L=(0,2,5,6)
L=(0,2,3,6)
L=(0,1,3,6)
L=(0,1,4,6)
L=(0,3,4,6)
L=(0,2,7,12)
L=(0,2,5,9)
for a from 1 to 5 do
for b from 1 to 5 do
for c from a to 5 do
(L=(0,a,a+b,a+b+c);
print L;
test L)

///

pureBetti=Degs-> (
--Input: Degs must be a strictly increasing list of positive integers
--Output: List of ranks of the minimal integral betti sequence that satisfy the
--"Peskine-Szpiro" equations
     if not isStrictlyIncreasing Degs then error "--pureBetti was given degrees that were not strictly increasing";
     c:= # Degs;
     p:=1;
     for i from 1 to c-1 do (for j from 0 to i-1 do p=p*(Degs_i-Degs_j));
     D:=for i from 0 to c-1 list(
         (-1)^i* product(i, j->Degs_j-Degs_i)*product(i+1..c-1, j->Degs_j-Degs_i));
     Bettis=for i from 0 to c-1 list (p/D_i);
     Bettis= apply(Bettis/(gcd Bettis), i->lift(i,ZZ)))

--Now some routines for displaying the answer:
--Input: Degs must be a strictly increasing list of positive integers
--Output: Hash table with the same content as the BettiTally that would display
--the Betti numbers given by pureBetti

pureBettiDiagram = Degs -> (
--The betti diagram of a pure degree sequence (generator of the ray, according
--to Boij-Soderberg; need not be an actual resolution.)
     Bettis:=pureBetti Degs;
     BB:=new MutableHashTable;
     scan(#Degs, i->BB#(i,{Degs_i},Degs_i)=Bettis_i);
     new HashTable from BB)


--input: a hash table similar to a BettiTally
--Output: the corresponding BettiTally
bettiH= H-> betti new BettiTally from H

///
load "BoijSoderberg.m2"
pureBetti{0,1,2,3,4}
B=pureBetti{0,2,3,4}
D1=pureBettiDiagram {0,2,3,4}
bettiH D1
///

rkSchur = (n,L)->(
--rank of a Schur functor on a module
--input: a non-neg integer n and a non-increasing sequence of non-neg integers L
--output: the rank of the representation S_L(C^n). Here (11111) represents an exterior power, (k) a symmetrci power.
     M:=L;
     if #M<n then M=L|toList(n-#M:0);
     det map(ZZ^n, ZZ^n, (i,j)->binomial(M_i+n-1-i+j, n-1)))

///
rkSchur(6,{1,1,1,1}) -- exterior power
rkSchur(6,{2}) -- symmetric power
rkSchur(3,{3,2,0})
rkSchur(3,{4,3,1}) -- the previous tensored with the top exterior power
///

--sequence of ranks in Weyman's complex for a degree list L={d0,d1..dn}
--Note that the list E is (in Weyman's notation) {e1-1..en-1}.
--The list D is {d1-d0, d2-d0, .. , dn-d0}

Weyman = L->(
     --Note: we don't really need to compute all the Betti numbers here; just
     --the pureBetti and the multiplier. (Original version did them all, to check...)
     --in fact, R_0=rkSchur(#D,lambda).
     D:=for i from 1 to #L-1 list L_i-L_0;
     E0:=for i from 1 to #D-1 list  D_(i)-D_(i-1)-1;
     E:={D_0-1}|E0;
     Eplus1:=E+toList(#D:1);
     lambda = for i from 1 to #D list sum E_{i..#D-1};
     A:={lambda}|for i from 0 to #D-1 list(
	  lambda+ (Eplus1_{0..i}|toList(#D-1-i:0)));
     P:=pureBetti L;
     R:=apply(A, a->rkSchur(#D,a));
     multiplier:=R_0/P_0;
     << "-- "<< multiplier << "x" << pureBetti L << " = " << R;
     R_0
     )
///
load "BoijSoderberg.m2"
Weyman(0,1,2,3,4)
A
lambda
Weyman(0,1,3,4)
W=Weyman {0,4,6,9,11}
P=pureBetti(0,4,6,9,11)
for i from 0 to #W-1 list (W_i/P_i)
///

--take a betti table or hash table to the sequence of degrees in its lowest row.

--Input: a hash table or BettiTally
--Output: the length of the free resolution it represents.

--projectiveDimension = B -> max apply ((keys B), i->i_0) 
--     max apply ((keys B), i->i_0);
projectiveDimension = B -> (
     BB=select(keys B,i->not(B#i==0));
     max apply(BB, i->i_0))


--Input: a hash table or BettiTally
--Output: the sequence of degrees of the components of the free modules having lowest degree;
--that is the "top elements" of the betti diagram. exit with an error if there is not some
--nonzero entry in each place.
lowestDegrees = B->(
     BL=apply(1+projectiveDimension B, m->min(apply (keys B, i->if i_0==m and B#i!=0 then i_2 else infinity)));
     apply(BL, i-> if i == infinity then error "lowestDegrees applied to betti table with col of zeros");
     BL)
--Same as lowestDegrees, but for the "bottom elements"
highestDegrees = B->(
     BL=apply(1+projectiveDimension B, m->max(apply (keys B, i->if i_0==m and B#i!=0 then i_1 else -infinity)));
     apply(BL, i-> if i == -infinity then error "lowestDegrees applied to betti table with col of zeros");
     BL)
///
load "BoijSoderberg.m2"
m=matrix"1,0,0;
0,1,1;
0,0,1"
B=mat2betti m
lowestDegrees B
m=matrix"1,0,0;
0,0,1;
0,0,1"
B=mat2betti m
lowestDegrees B
///


--input: list of rational numbers
--output true if the list is strictly increasing, else false.
isStrictlyIncreasing=L->(
     t:=true;
     for i from 0 to #L-2 do t=(t and (L_i<L_(i+1)));
     t)

///
L={1,4,5,9}
isStrictlyIncreasing L==true
L={1,4,5,9,9}
isStrictlyIncreasing L==false
///

--input: a BettiTally or a similar hash table
--output: a triple, 
--First element: the first summand in the (conjectural) Boij-Soderberg decomposition
--second element: the multiplier
--third element: the result of subtracting it.
decompose1= B->(
     L:=lowestDegrees B;
     if not isStrictlyIncreasing L then print "NOT IN THIS SIMPLEX OF PURE BETTI DIAGRAMS";
     C:=pureBettiDiagram L;
     ratio:=min apply(#L, i->(B#(i,{L_i}, L_i))/(C#(i,{L_i},L_i)));
     (C,ratio,merge(B,C, (i,j)->i-ratio*j))
     )

--input: a BettiTally or a similar hash table
--output: The routine prints the Boij-Soderberg summands.
--prints "not in convex hull" if the given BettiTally is not in the convex
--hull of the allowable pure betti diagrams. Prints an error message
--if the decomposition fails. Returns a list of the components as a list of pairs,
--each a rational coefficient followed by a hash table representing a pure betti diagram,
--if it succeeds.
decomposeAll = B->(
     Components:={};
     B1:= new MutableHashTable from B;
     while min values B1 >= 0 and max values B1 >0 do (
	  X:=decompose1(new HashTable from B1);
	  B1=new MutableHashTable from X_2;
	  --change the type of the values in X_0 to ZZ
	  Y=new HashTable from apply(pairs X_0, i->{first i, lift(last i, ZZ)});
	  print(X_1,bettiH Y);
	  Components = Components | {X_1, Y});
	       Components)

-- input is a matrix over ZZ or QQ
-- output is the corresponding BettiTally 
mat2betti = method()
mat2betti Matrix := (M) -> (
     e := entries M;
     a := flatten apply(#e, i -> 
	  apply(#e#i, j -> (j, {i+j}, i+j) => if e#i#j != 0 then e#i#j else null));
     a = select(a, b -> b#1 =!= null);
     new BettiTally from a
     )

///
restart
load "boijSoderberg.m2"
matrix "1,0,0,0;
        0,4,4,1"
mat2betti oo	
decomposeAll oo


///

       fromDualMatrix = (f) -> (
           R := ring f;
           d := first max degrees source f;
           g := product apply(generators R, v -> v^d);
           f1 := contract(transpose f, matrix{{g}});
	   modulo(f1,target f1 ** matrix table(1, numgens R, (i,j) -> R_j^(d+1))))


--Given a strictly increasing degree sequence L and a number of gneerators m,
--this routine produces a "generic" module of finite length with the 
--m generators and number of socle elements  and regularity corresponding
--to the pure resolution with degree sequence L. The module is constructed
--by taking a certain number of generic elements inside an appropriate direct
--sum of copies of a zero-dimensional complete intersection. We use the fact
--that in a polynomial ring in c variables, 
--modulo the r+1 st power of each variable, the part of
--generated in degree (c-1)r looks like the part of the injective hull
--of the residue class field generated in degree -r.

testSocle=(L,m)->(
     c:=#L-1; -- codimension
     r:=last L-first L-c; -- regularity
     s:=c*r; -- socle degree mod (vars)^[r+1]
     R:=kk[vars(0..c-1)];
     B:=pureBetti L;
     f:=random(R^(m*B_c), R^{m*B_0:-s+r});
     betti res (M=image (f**(R^{s-r}/(ideal gens R)^[r+1]))))
///
L={0,1,3,4}
pureBetti L
testSocle(L,1)
testSocle(L,3)
///
testGenerators=(L,m)->(
     c:=#L-1; -- codimension
     R:=kk[vars(0..c-1)];
     B:=pureBetti L;
     betti res coker (M=random(R^{m*B_0:-L_0}, R^{m*B_1:-L_1})))
///
kk=ZZ/5
L={0,4,9,10}
pureBetti L
B=testGenerators(L,2) -- gives a pure resolution not too infrequently.
///

--takes a list of degrees, outputs the Hilb function of the corresponding
--pure resolution.

pureHilb = L->(
B:=pureBetti L;
n:=length L -1;
LL=for i from 0 to 10 list --max L-n+1 list
     sum(for j from 0 to n when L_j<=i list (-1)^j*binomial(n-1+i-L_j, n-1)*B_j);
LL)--/(sum LL))

Betti2Hilb = B ->(
BB:=new HashTable from B;
numvars:=max((keys BB)/first);
startdeg:=min((keys BB)/last);
regB :=max((keys BB)/last)-numvars;
Blist :=for j from startdeg to regB list
     sum(keys BB, k->(-1)^(first k)*(if last k == j then BB#k else 0));
for j from startdeg to regB list
     sum(j+1, t->binomial(numvars-1+j-t, numvars-1)*Blist_t)
)

hashTable2Hilb = B ->(
BB:=B;
numvars:=max((keys BB)/first);
startdeg:=min((keys BB)/last);
regB :=max((keys BB)/last)-numvars;
Blist :=for j from startdeg to regB list
     sum(keys BB, k->(-1)^(first k)*(if last k == j then BB#k else 0));
for j from startdeg to regB list
     sum(j+1, t->binomial(numvars-1+j-t, numvars-1)*Blist_t)
)
HilbList= L-> for i from 0 to #L-1 list(if i%2==0 then L_i else hashTable2Hilb L_i) 
///
restart
load "BoijSoderberg.m2"
P0=matrix"1,0,0,0;
       0,3,0,0;
       0,1,6,3"
B=mat2betti P0
BB=new HashTable from B
{1,3,3}==Betti2Hilb B
HilbList decomposeAll B
///


--takes a betti tally and tests whether it is a pure resolution
isPure =B->(length keys B == 1+max ((keys B)/first))


--HPR=ZZ[tt,b_0..b_n] -- Hilbert Poly Ring
--bs=(vars HPR)_{1..n+1} -- Betti Sequence

bin=alpha->product(n-1,i->alpha+tt+n-1-i) --binomial coeff numerator

hp=method() --hilb poly as a funct of betti numbers b_i (vars) in degree d_i (in ZZ).
hp(List):=a->sum(#a,i->(-1)^i*b_i*bin(-a_i))

bettiNumbers=a->matrix {pureBetti a}

--bettiNumbers=method()
--bettiNumbers(List):=a->(pp:=hp(a); -- a is the list of degrees
     --returns betti nums of a pure complex
--     pcoef:=(coefficients(pp,Variables=>{tt}))_1;
--     bb:=transpose syz substitute(diff(bs,pcoef),ZZ);
--     if bb_0_0>0 then bb else -bb)
rangeOK=method()
--rangeOK(List,ZZ,ZZ):=(d,r,n)->#d==n+1 and 0<= d_0 and 
--   apply(n,i-> d_i<d_(i+1))==toList(n:true) and d_n<=r+n 
   --tests whether degree seq is non-neg, strictly increasing, of the right length n, and last elt
   -- is bounded by reg + num vars, and 
rangeOK(List,ZZ,ZZ,ZZ):=(d,lowestDegree, highestDegree, n)->
#d==n+1 and lowestDegree<= d_0 and apply(n,i-> d_i<d_(i+1))==toList(n:true) and d_n<=highestDegree+n 
   --tests whether degree seq is >=lowestDegree, strictly increasing, of the right length n, and last elt
   -- is bounded by highestDegree + num vars.

bettiMatrix=method()
--bettiMatrix(List):=d->(
     --betti matrix of a pure complex from list of degs
--     if  rangeOK(d,r,n) then (
--     bb:=bettiNumbers(d);
--     matrix apply(r+1,i->apply(n+1,j->if (d_j)==i+j then bb_(0,j) else 0))
--     ) else error( "wrong Range"))
bettiMatrix(List,ZZ,ZZ):=(d,lowestDegree,highestDegree)->(
     --betti matrix of a pure complex from list of degs
     n:=#d-1;
     if  rangeOK(d,lowestDegree,highestDegree,n) then (
     bb:=bettiNumbers(d);
     r:=highestDegree-lowestDegree;
     	  map(ZZ^(r+1),ZZ^(n+1), (i,j)->
	       if d_j==lowestDegree+i+j then bb_(0,j) else 0)
          --matrix apply(r+1,i->apply(n+1,j->if (d_j)==i+j then bb_(0,j) else 0))
     ) else error( "wrong Range"))

///
restart
load"BoijSoderberg.m2"
d={0,1,3}
bettiMatrix(d,-1,3)
///
nextLower=method()
nextLower(List, ZZ, ZZ):=(d,lowestDegree, highestDegree)->(
	  --returns A deg seq adjacent to d and below it (chooses one such)
	  n:=#d-1;
          if d_0>lowestDegree then join( {d_0-1},d_{1..n}) 
	  else if d_0==lowestDegree then(
	  k:=1; 
	  while (d_k-1==d_(k-1) ) do (k=k+1);
	  join(d_{0..k-1},{d_k-1},d_{k+1..n}))
          else error("lowestDegree is too high"))

nextUpper=method()
nextUpper(List, ZZ, ZZ):=(d,lowestDegree, highestDegree)->(
	  --same but above
	  n:=#d-1;
	  if d_n<n+highestDegree then join(d_{0..n-1},{d_n+1}) 
	  else if d_n==n+highestDegree then
	  (k:=n; 
	  while (d_k-1==d_(k-1) ) do (k=k-1);
	  join(d_{0..k-2},{d_(k-1)+1},d_{k..n}))
     	  else error"highestDegree is too low")

lowerRange=method()

lowerRange(List,ZZ,ZZ):=(d,lowestDegree, highestDegree)->(
	  --returns a maximal chain of deg seqs below d
	  n:=#d-1;
	  rangeOK(d,lowestDegree, highestDegree,n);
	  A:={d};
	  if d =!= toList(lowestDegree..n+lowestDegree)  then ( 
          e:=nextLower(d,lowestDegree,highestDegree);
	  A=join(A,lowerRange(e,lowestDegree,highestDegree)));
     	  A)

upperRange=method()

upperRange(List,ZZ,ZZ):=(d,lowestDegree, highestDegree)->(
	  --returns a maximal chain of deg seqs below d
	  n:=#d-1;
	  rangeOK(d,lowestDegree, highestDegree,n);
	  A:={d};
	  if d =!= toList(highestDegree..n+highestDegree) then ( 
          e:=nextUpper(d,lowestDegree,highestDegree);
	  A=join(A,upperRange(e,lowestDegree,highestDegree))); --EEE
     	  A)

rangeMatrices=method()
rangeMatrices(List,ZZ,ZZ):=(e,lowestDegree,highestDegree)->( 
	       --takes a deg seq, returns list of mats, k-th has 
	       --a one in posn e_k-k-lowestDegree, k
	       n:=#e-1;
	       r:=highestDegree-lowestDegree;
               apply(n+1,k->
		    map(ZZ^(r+1), ZZ^(n+1),
			 (i,j)-> if i==e_k-k-lowestDegree and j==k then 1 else 0)  -- subtracted lowestDegree
		    )
	       )


peskineSzpiro=(r,n)->apply(n+r+1,k->matrix apply(r+1,i->apply(n+1,j->
--returns (redundant) list of n+r+1 Peskine-Szpiro relations in hilb function form
--(the Hilb fcn values from *** to ***) Note: the P-S eqns in this sense are
--\chi(O(m)\otimes M)= 0 .
	       (if k<r then 1 else (-1)^(k-r))*(-1)^(n-j)*
	       binomial(n+r-k-i-j+n-1,n-1)
	       )))
--PS=peskineSzpiro(r,n); 
--This was a global variable used in numericalComplex and flipEquation only

numericalComplex=A->(
     n:=rank source A-1;
     r:=rank target A-1;
     AA:=A;
     apply(n+r+1,i->(
	       PS:=peskineSzpiro(r,n); 
	       ss:=if i<=r then AA_(r-i,n) else AA_(0,n-i+r);
	       AA=AA-ss*PS_i;
	       ss)))
--The numerical complex that flips the "upper" eqn to the "lower" eqn, written
--as the sequence of coefficients of the PS-equations.

flipEquation=(A)->(
     n:=rank source A-1;
     r:=rank target A-1;
     aa:=numericalComplex(A);
     PS:=peskineSzpiro(r,n); 
     apply(n+r+1,c->A-sum(c,i->aa_(i)*PS_(i))))

upperEquation=(A)->(L:=flipEquation(A);L_(#L-1))
--the necessary lin comb of the PS equations.

///
restart
load "BoijSoderberg.m2"
d={0,1,4}
F=facetEquation(d,0,0,3)
numericalComplex F
flipEquation F
upperEquation F

d={0,3,4,5,8,10}
F=facetEquation(d,2,-3,10)
numericalComplex F
flipEquation F
upperEquation F

--Note: UpperEquation has zeros above and ON the places where the betti diagram
--for the degree sequence d is nonzero. But this fact follows from the vanishing of
--the lower equation at such sequences.
///


middleComplex=(d,e)->(
     n=#d-1;
     t:=1;
     L:=apply(n+1,i->(t=t*if d_i==e_i then 1 else -1 ));
     apply(n+1,c->if L_c==1 then e_c else d_c))

nextPure=(d,k)->if d_k+1==d_(k+1) and (k==#d-2 or d_(k+2)>d_(k+1)+1) then 
     apply(#d,i->if i<k or i>( k+1) then d_i else d_i+1) else error("no next pure sequence")
--in the case of two degree sequences differing by one in two consec places, computes
--the degree sequence in between.



facetEquation=method();

facetEquation(List,ZZ,ZZ,ZZ):=(d,i,lowestDegree, highestDegree)->(
     --i an integer between 0 and #d-2
     --d a strictly increasing list of integers 
     --such that d_(i+1)=d_i+1
     --lowestDegree < highestdegree, integers 
     --lowest degree should be <=d_0, highestDegree-lowestDegree >=d_n-n, and >=d_n-n+2 when i=n-1,
     --where n=#d-1.
--routine produces the "upper" equation of the supporting hyperplane
--of the facet corresponding to d< (...d_i+1, d_(i+1)+1,...)=nextpure(d,k).
--the equation is presented as a 
-- map ZZ^(#d) --> ZZ^(highest-lowest+1).
     n:=#d-1;
     rangeOK(d,lowestDegree,highestDegree,n);
     if d_i+1<d_(i+1) then error("innapropriate value of i");
     e:=nextPure(d,i);
     A:=matrix apply(lowerRange(d,lowestDegree, highestDegree),
	  c->join(toSequence entries bettiMatrix(c,lowestDegree,highestDegree)));
     B:=matrix apply(upperRange(e,lowestDegree,highestDegree),
	  c->join(toSequence entries bettiMatrix(c,lowestDegree,highestDegree)));
     C:=matrix apply(rangeMatrices(e,lowestDegree,highestDegree),c->join(toSequence entries c));
     D:=(entries transpose syz(A||B||C))_0;
     F:=matrix apply(highestDegree-lowestDegree+1,i->apply(n+1,j->D_((n+1)*i+j)));
     de:=middleComplex(d,e);
     B1:=bettiMatrix(de,lowestDegree,highestDegree);
          if dotProduct(F,B1)>0 then F else -F)


///
restart
load "BoijSoderberg.m2"
d={0,1,4}
e=nextPure(d,0)
facetEquation(d,0,-1,3)

d={0,3,5,6}
facetEquation(d,2,-3,4) -- OK
facetEquation(d,2,0,3) -- gives error msg.

d={0,1,3}
facetEquation(d,0,0,0)
--gives error msg

d={0,1,3}
facetEquation(d,0,-1,1)
facetEquation(d,0,0,2)
d={0,2,3}
facetEquation(d,1,-2,2)



d={1,3,4,5,7}
facetEquation(d,2,1,3)
bettiH pureBettiDiagram d
d={5,7,8,11}
facetEquation(d,1,5,8)
facetEquation(d,1,0,8)
d={5,7,9,10}
///

dotProduct=method()

dotProduct(Matrix, Matrix):=(A,B)->
--dot product of matrices as vectors
     sum(rank target A,i->sum(rank source A,j->A_(i,j)*B_(i,j)))

dotProduct(HashTable, HashTable):=(A,B)-> --Gets in the way of another method
     --dot product of two hash tables with similar structure
     sum(keys A, k->(if B#?k then return (B#k) * (A#k) else return 0))

dotProduct(Matrix, ZZ, BettiTally):=(A,lowest, B)->(
     --lowest is an integer specifying what degree the first row of A is supposed to have.
     nr=rank target A;
     highest=nr+lowest-1;
     nc=rank source A;
     d0=min((keys B)/last);
     regB=max(((keys B)/last)-(keys B)/first);
     lengthB=max((keys B)/first);
     if d0<lowest then error "matrix A begins in too high a degree";
     if regB>highest then error "matrix A stops in too low a degree";
     if nc < 1+lengthB then error "matrix A has too few columns";
     sum(keys B, k-> (B#k)*(A_(last k-first k-lowest, first k)))
     )


supportFunctional=method()

supportFunctional(ChainComplex, ChainComplex):=(E,F)->(
     --E should be a chain complex starting in degree 0 and going to negative degrees.
     --F should be a chain complex starting in a postive degree and going to degree 0
     -- the code is meant to execute 
     --\langle E, \beta\rangle = \sum_{j\leq i}(-1)^{i-j}\sum_k\beta_{i,k}h_{-k}(H^j(E)),
     --
lengthF=length F;
degreesF=flatten (for i from 0 to lengthF list flatten degrees F_i);
minF = min degreesF;
maxF = max degreesF;
HHE=HH E;
L=for i from 0 to length E list matrix{{hf(minF..maxF, (HH E)#(-i))}};
A=transpose L_0;
for i from 1 to length L -1 do A = A|(transpose L_i);
AA=map(ZZ^(maxF-minF-lengthF+1), ZZ^(lengthF+1), (p,q)->
     sum(0..min(q,length E), 
	  j->if HHE#?(-j) then (-1)^(q-j)*hilbertFunction(-p-q, (HHE)#(-j)) else 0));
dotProduct(AA, minF, betti F)
     )

supportFunctional(ChainComplex, BettiTally):=(E,B)->(
     --E should be a chain complex starting in degree 0 and going to negative degrees.
     --F should be a chain complex starting in a postive degree and going to degree 0
     -- the code is meant to execute 
     --\langle E, \beta\rangle = \sum_{j\leq i}(-1)^{i-j}\sum_k\beta_{i,k}h_{-k}(H^j(E)),
     --
lengthF=max apply(keys B, K->first K);
degreesF=apply(keys B, K->last K);
minF = min degreesF;
maxF = max degreesF;
HHE=HH E;
L=for i from 0 to length E list matrix{{hf(minF..maxF, (HH E)#(-i))}};
A=transpose L_0;
for i from 1 to length L -1 do A = A|(transpose L_i);
AA=map(ZZ^(maxF-minF-lengthF+1), ZZ^(lengthF+1), (p,q)->
     sum(0..min(q,length E), 
	  j->if HHE#?(-j) then (-1)^(q-j)*hilbertFunction(-p-q, (HHE)#(-j)) else 0));
dotProduct(AA, minF, B)
     )

randomDegreeSequence=(n,maxdegshift)->(
     accumulate(plus, 0, apply(n+1, j->1+random (maxdegshift-1))))

///
restart
load "BoijSoderberg.m2"
kk=ZZ/32003
S=kk[x_1..x_4]
d={1,3,4,5,7}
B=bettiH pureBettiDiagram d
Be=bettiH pureBettiDiagram (e=nextPure(d,2))
n=4;r=3;
Bde=bettiH pureBettiDiagram middleComplex(d,e)
A=facetEquation(d,2,1,3)
dotProduct(A,1,B)
dotProduct(A,1,Be)
dotProduct(A,1,Bde)
///

///
restart
load"BoijSoderberg.m2"
kk=ZZ/32003
S=kk[x_1..x_3]
E1=res (S^1/ideal(x_1^2, x_2^3, x_3^4))
E=Hom(chainComplex(transpose E1.dd_2, transpose E1.dd_1), S^1)
betti E
betti E1
time for i from -5 to 20 do
print supportFunctional(E**S^{i},E1)
time for i from -5 to 20 do
print supportFunctional(E**S^{i},betti E1)

B=betti E1
max apply(keys B, K->first K)
///

betti2matrix=B->(
     --input: a betti Tally
     --output a matrix of integers, the entries of the betti table, and an integer,
     --the "degree" that the 0,0 entry should have.
lowest := min((keys B)/last);
highest:=regularity B;
leng :=max((keys B)/first);
BB:=mutableZero(ZZ,highest-lowest+1, leng+1);
apply(keys B, k-> (BB_(last k-first k, first k)=(B#k)));
(matrix BB, lowest)
)

///
kk=ZZ/2
S=kk[a,b,c]
m=random(S^2,S^{5:-1})
B=betti res coker m
betti2matrix B
     )
///

Bott=method()
Bott(List, ZZ):=(L,u)->(
     --given a weakly decreasing list of integers L of length n and an integer u,
     --uses Bott's algorithm to compute the cohomology of the vector bundle 
     -- E=O(-u) \tensor S_L(Q), on P^n = PP(V)
     --where Q is the tautological rank n quotient bundle in the sequence 
     --   0--> O(-1) --> O^(n+1) --> Q -->0
     --and S_L(Q) is the Schur functor with the convention S_(d,0..0) = Sym_d, S_(1,1,1) = \wedge^3 etc.
     --returns either 0, if all cohomology is zero,
     -- or a list of three elements: A weakly decreasing list of n+1 integers M;
     -- a number i such that H^i(E)=S_M(V); and 
     -- the rank of this module.
     M=new MutableList from join(L,{u});
     i:=0;
     j:=#M-1;
     while j>0 do(
     	  while M#(j-1)>=M#j and j>0 do j=j-1;
	  if j==0 then break;
     	  if M#j==M#(j-1)+1 then return 0 else (
	       i=i+1;
	       k:=M#(j-1);
	       M#(j-1)=(M#j)-1;
	       M#j=k+1;
	       j=#M-1);
	         );
	    	 M=toList apply(M, t->t-(last M));
	  {M,i, rkSchur(#M,M)}
     )

Bott(List,ZZ,ZZ):=(L,low,high)->(
     --produces the betti diagram of the tate resolution of the sheaf S_L(Q),
     --between the column whose index is "low" and the column whose index is "high"
     n:=#L;
     r:=high-low-n;
     V:= mutableMatrix map(ZZ^(n+1),ZZ^(r+1), 0);
     apply(high-low+1, u->(
	       B:=Bott(L,-(low+u));
	       if not B===0 then V_(n-B_1,u-(n-B_1))=B_2)
	  );
     matrix V
     )
     


///
restart
load "BoijSoderberg.m2"
Bott({3,2,1},-10,0)
Bott({0,0,0},-5,5)

L={0,0,0}
for u from 0 to 6 do
print Bott(L,u)
L={5,2,1,1}
for u from 0 to 10 do
Bott({0,0},-1)
print Bott(L,-u)
///

randomDegs=(len, step, elevator)->(
          l = {0};
       currentNum = 0;
       for i from 0 to len-2 do (
       if i == elevator then (
	         currentNum = currentNum + 3;
	        l = append(l, currentNum-2);
	        l = append(l, currentNum);
	            ) else (
	        currentNum = currentNum + random(step) + 1;
	    	          l = append(l, currentNum);
	             )       
	        );
	      return l;
	   )
///
restart
load "BoijSoderberg.m2"
randomDegs(6,4,3)
///

---------------------------------------------------
----------Routines for the Tate resolution-----------
----------------------------------------------------				
testStrictlyIncreasing = Z->
  scan(1..length Z-1, i->if Z_i-Z_(i-1)<0  then error("List is not strictly increasing"))
testStrictlyDecreasing = Z->
  scan(1..length Z-1, i->if Z_i-Z_(i-1)>0  then error("List is not strictly decreasing"))

findPosition=(x,Z)->(
--returns largest j such that x>Z_j, or length Z if there is no smaller j.
     testStrictlyDecreasing Z;
     j:=0;
     while j<length Z and x<=Z_j do j=j+1;
     j)
///
load "BoijSoderberg.m2"
Z={5, 2,0,-3}
for x from min Z-1 to max Z+1 do print (x,findPosition(x,Z))
///          

pureTate=(Z,b,B)->(
testStrictlyDecreasing Z;
m:=length Z;
T= new MutableHashTable;
i=0;
j:=0;
for i from b-m to B do(
j=findPosition(i,Z);
T#(j,i)=abs product(Z, z->i-z));
g:=gcd apply(keys T, k->T#k);
--replace the previous line by g:=1; to get the values of the polynomial
map(ZZ^(m+1), ZZ^(B-b+1), (j,i)-> 
     if T#?(m-j,b+i-m+j) 
     then T#(m-j,b+i-m+j)//g
     else 0)
)


nextDown=(Z,low)->(
     testStrictlyDecreasing Z;
     --returns the next root sequence W below Z if there is one
     --with the last (smallest) 
     --element of W at least low-#Z , or "false" if there is none such.
     k:=-1;
     if #Z==1 then k=0 else while(k=k+1;Z_k==Z_(k+1)+1 and k< #Z-2 ) do (); 
     if k==#Z-2 and Z_k==Z_(k+1)+1 then k=k+1;
     W:=apply(#Z,j->if j<k or j>k then Z_j else Z_j-1) ;
     if W_(#Z-1)<low-#Z then false else W)

///
restart
load "BoijSoderberg.m2"
Z={4,2}
for i from 1 to 7 do print (Z=nextDown(Z, 1))
Z={0}
Z=nextDown(Z, -3)
///

--The next two routines produce the root sequences adjacent to Z, 
--when the i-th term of Z is used as the facet center.
Zplus=(Z,i)->(
     --the prev version wouldn't work if i=0 or i=#Z-1, both of which should be ok!
     if i>0 then if  Z_(i-1)==Z_i+1 then error "bad face data";
	  apply(Z,z->if z=!=Z_i then z else z+1))
     
Zminus=(Z,i)->(	  
     	  if i<#Z-1 then if Z_(i+1)==Z_i-1 then error "bad face data";
	    apply(Z,z->if z=!=Z_i then z else z-1))
///
restart
load "BoijSoderberg.m2"
Z={1,0,-1}
Z={4,2,0}
Zplus(Z,0)
Zplus(Z,1)
Zplus(Z,2)
Zminus(Z,0)
Zminus(Z,1)
Zminus(Z,2)
///
	
facetTate=(Z,i,low,high)->(
          testStrictlyDecreasing Z;
     if i>0 then if  Z_(i-1)==Z_i+1 then error "bad face data";
     if i<#Z-1 then if  Z_(i+1)==Z_i-1 then error "bad face data";
	  Zm:=apply(Z,z->if z=!=Z_i then z else z-1);
	  Zp:=apply(Z,z->if z=!=Z_i then z else z+1);
	  A:={pureTate(Zm,low,high)};
	  while(Zm=nextDown(Zm,low);class Zm===List) do A=join(A, {pureTate(Zm,low,high)});
	  m:=#Z;
	  Zeroes:=join toSequence apply(#Z,i-> join apply(toList (Zp_i+1+i..high),j-> 
		    matrix apply(#Z+1,k->apply(toList(low..high),l->if k==m-i and l==j then 1 else 0)
			 )));
	  Zeroes2:=join apply(toList (low..high),j->
	       matrix apply(#Z+1,k->apply(toList(low..high),l->if k==0 and l==j then 1 else 0)
		    ));
	  B:=flatten Zeroes_0;
	  apply(A,M-> (B=B||flatten M;));
	  apply(Zeroes,M->(B=B||flatten M;));
	  apply(Zeroes2,M->(B=B||flatten M;));
	  B1:=syz B;
	  matrix apply(m+1,i->apply(high-low+1,j->B1_0_(j*(m+1)+i)))
	  )

degreeSequence=(Z,i)->(ds=join(apply(i,j->Z_j),{Z_i+1,Z_i,Z_i-1},apply(toSequence(i+1..#Z-1),j->Z_j));apply(#ds,i->-ds_i))

///
restart
load "BoijSoderberg.m2"
Z={0}
pureTate(Z, -6, 6)
Z={2,0}
pureTate(Z, -6, 6)
Z={2,0, -2}
Z={5,3,2,0,-2,-5,-6}	  
pureTate(Z,-6,6)
pureTate(Zplus(Z,4),-6,6)
pureTate(Zminus(Z,4),-6,6)
d=degreeSequence(Z,4)
bettiMatrix(d,-6,6)
facetTate(Z,4,-6,6)	  
///

ZtoD=(Z,t)->(d:={};
for i from 0 to #Z-1 do d=append(d, -Z_i);
sort flatten append(d, {-Z_t+1, -Z_t-1})
)


facetFormula=method()
facetFormula(List, ZZ, ZZ, Sequence):=(d, c, t, Bounds)->(
     --reproduces the dual Tate table < - , F >_{c,tau} corresponding to
     --F, a pure free resolution of degree sequence d
     --index t (tau in our text)
     --degree c.
--<E,F>_{c,\tau}= 
--       \sum_{(A)\cup (B)\cup(C)}
--        (-1)^{i-j} \beta_{i,k} h^j(\cE(-k))
--	A&=& \{i,j,k\mid  j\leq i-2\} \cr
--	B&=& \{i,j,k\mid   i-1 \leq j\leq i  \hbox{ and } j< \tau\} \cr
--	C&=& \{i,j,k\mid  i-1 \leq j\leq i  \hbox{ and } j= \tau \hbox{ and } k\leq c+(i-j)\}
low:=Bounds_0;
high:=Bounds_1;
T:=new MutableHashTable;
m:=#d-2;
bb:=pureBetti d;
--range A
apply(#d, i->(for j from 0 to i-2 do T#(j,-d_i)=(-1)^(i-j)*bb_i));
--range B
apply(#d, i->(for j from max(0,i-1) to i do if  j<t then T#(j,-d_i)=(-1)^(i-j)*bb_i));
--range C
apply(#d, i->(for j from max(0,i-1) to i do if  j==t and -d_i<=c+i-j then T#(-d_i,j)=(-1)^(i-j)*bb_i));
toTateTable(T,m,low,high)
)

--and the version for root sequences:
facetFormula(List, ZZ, ZZ,ZZ):=(Z, t, low, high)->(
d:=ZtoD(Z,t);
facetFormula(d,d_t,t+1,(low,high))
)

toTateTable = (T, m, low, high)->(
     --takes a hashTable T with entries (j,k)=>x_{j,k} and puts 
     --x_{j,k} into the appropriate place representing h^j cE(k) in a Tate resolution matrix.
     --Here the appropriate entry for the (p,q) place is h^{m-p} cE(q+low+(m-p))
     --x_{m-p,this place is the k-low+j column and the m-j row
map(ZZ^(m+1), ZZ^(high-low+1), (p,q)-> 
     if T#?(m-p,q+low-(m-p))
     then T#(m-p,q+low-(m-p)) 
     else 0)
)     

///
restart
load "BoijSoderberg.m2"
Z={0,-4,-7}
facetFormula(Z,1,-10,10)
facetTate(Z,1,-10,10)
facetFormula(Z,0,-10,10)
facetTate(Z,0,-10,10)
--wrong signs!
///

----------------------------------															
end 
----------------------------------

restart
load "BoijSoderberg.m2"

--the following is OK for the B-S conjecture iff D<=3
D=3
B=matrix{{2,4,D,0},{0,D,4,2}}
BB=mat2betti B
decomposeAll BB


i=ideal"a2,b3,c5"
B=betti res i
decomposeAll B

m=matrix"1,0,0,0,0,0;
0,10,16,10,0,0;
0,0,10,16,10,0;
0,0,0,0,0,1"

m=matrix"1,0,0,0,0,0;
0,10,16,12,0,0;
0,0,12,16,10,0;
0,0,0,0,0,1"
m=matrix"1,0,0,0;
0,0,0,0;
0,3,0,0;
1,3,3,1;
0,0,3,0;
0,0,0,0;
0,0,0,1"

B=mat2betti m
decomposeAll B

S=kk[a,b,c,d]
i=ideal"a2,b3,c5,d7"
decomposeAll betti res i


S=kk[vars(0..7)]
M=genericMatrix(S, 2, 4)
I=minors (2,M)
B=betti res I
decomposeAll B

i=ideal"a2,b3,c5,d7"
B=betti res i
decomposeAll B


f=matrix"a3,b3,cde2;b,c,d2"
f_(1,1)
fromDual f
betti res ideal oo

S=kk[a,b]
--assume f has target degrees 0
f=matrix"a,b"
betti res coker fromDual f
f=matrix"a;b"
first max degrees source f

restart
load "BoijSoderberg.m2"
testSocle({0,3,7},1)
Weyman({0,3,7})
testSocle({0,4,12},1)
Weyman({0,4,12})

testSocle({0,1,4,5},10)
bettiH pureBettiDiagram{0,1,4,5}
bettiH pureBettiDiagram({0,2,3,5})

S=kk[a,b,c]
betti res ideal random(S^1, S^{8:-3})

--hope: testSocle might give pure resolutions of type
--0,d,d+1,d+2....d+k, d+k+e -- this seems to work!
S=kk[a,b,c]

for e1 from 1 to 10 do(
     for e2 from 1 to 5 do(
     	  L={0,e1,e1+1,e1+e2+1};
	  print (#testSocle(L,1))))

S=kk[a,b,c,d]
for e1 from 1 to 7 do(
     for e2 from 1 to 7 do(
     	  L={0,e1,e1+1,e1+2,e1+e2+2};
	  print (#testSocle(L,1))))




L={0,3,4,5,8}
testSocle(L,1)

L={0,1,2,8}
testSocle(L,1)

-----------

L={0,2,3,5,7,8}
time testSocle (L,1)

--time testSocle (L,3)
--Does NOT give a pure resolution!
Weyman L
L={0,2,4,6,7}
testSocle (L,2)
--not pure, not right degrees

L={0,2,5,6}
pureBetti L --{2,5,8,5}
testSocle (L,1)
Weyman {0,2,7,13}

testSocle (L,7)

--not pure! not right degrees

--try the dual sequence
L={0,1,4,6}
pureBetti L --{5,8,5,2}
testSocle (L,1)
--testSocle (L,8)
--also not pure! not right degrees

L={0,1,4,6}
pureBetti L
testSocle (L,1)

--2 variables:
restart
load "BoijSoderberg.m2"


pureBetti L
S=kk[a..e]
I=(ideal vars S)^[3] -- socle degree is 10
f= random(S^7, S^{3:-(10-3)});
M=(image f)/(I*target f);
betti res M

----
generic cubics in 4 vars

S=kk[a,b,c,d]
i=ideal random(S^1, S^{5:-3})
betti res i
j=ideal"a5,b5,c5,d5"
betti res ((module (i+i))/(module j))

---------
--Steven Sam's example:
R is the polynomial ring QQ[x_1, ..., x_9]
and M is the cokernel of the map f: R^5 --> R defined by 
f = matrix {{ 
	  x_1^2 * x_3^4 - x_5^6 * x_7^8 + x_9^10, 
	  x_2*x_4 - x_6*x_8^3, 
	  x_1 * x_2 * x_3^5 + x_4^7, 
	  x_4^4 - x_1 * x_2^5, 
	  x_9 - x_8 * x_1^5 }}

----
restart
load "BoijSoderberg.m2"
kk=ZZ/32003
R=kk[x_1..x_9]
i=ideal(x_1^2 * x_3^4 - x_5^6 * x_7^8 + x_9^10, 
	  x_2*x_4 - x_6*x_8^3, 
	  x_1 * x_2 * x_3^5 + x_4^7, 
	  x_4^4 - x_1 * x_2^5, 
	  x_9 - x_8 * x_1^5)
B=betti res i
codim i
decomposeAll B

kk=ZZ
R=kk[x_1..x_4]
i=ideal( -9*x_1*x_2+8*x_2^2-4*x_1*x_3+3*x_2*x_3+5*x_3^2+9*x_1*x_4-x_2*x_4+6*x_3*x_4-8*x_4^2,
	  9*x_1+9*x_2+9*x_3+9*x_4,
	  3*x_3-2*x_4,
	  3*x_1+10*x_2-2*x_3+4*x_4)
B=betti res i
codim i

decomposeAll B
length res coker gens i

matrix {{ 
	  -9*x_1*x_2+8*x_2^2-4*x_1*x_3+3*x_2*x_3+5*x_3^2+9*x_1*x_4-x_2*x_4
	  +6*x_3*x_4-8*x_4^2,
	  9*x_1+9*x_2+9*x_3+9*x_4,
	  3*x_3-2*x_4,
	  3*x_1+10*x_2-2*x_3+4*x_4 }}
betti res coker oo

---
restart
load "BoijSoderberg.m2"
kk=ZZ/101
S=kk[x_(1,1)..x_(5,5)]
M=transpose genericMatrix(S,x_(1,1),5,5)
i=minors(2,M)
time( B=betti res i)

--------
Does B-S work for the 11 points in P^6??
restart
load "BoijSoderberg.m2"
load "points.m2"
S=kk[a..g] -- P6
i=randomPoints(S,11,0)
betti i
degree i
B=betti res i
decomposeAll B
--yes!
----------------
restart
load "BoijSoderberg.m2"
--Which degree sequences *could* come from cyclic modules?
for e1 from 20 to 20 do
     for e2 from 1 to 20 do
     	  for e3 from 1 to 20 do
	  (if e3==1 then print {e1,e2};
	   E={e1,e2,e3};
	   D={0}|accumulate(plus, {0}|E);
	   L=pureBetti D;
	   B=bettiH pureBettiDiagram D;
	   if first L == 1 and gcd E == 1 then 
	        if not B==testSocle(D,1) and not B== testGenerators(D,1) 
		then print(E,L))

print decomposeAll oo
Cyclic modules with shifts up to e=10,10,10,

({1, 1, 1}, {1, 3, 3, 1}) -- koszul	
({1, 2, 1}, {1, 2, 2, 1}) -- double is the generic module; this one doesn't exist

({2, 1, 1}, {1, 6, 8, 3}) -- Eagon Northcott (square of max ideal)
({2, 1, 2}, {1, 5, 5, 1}) -- Linear 5x5 Pfaffian

({3, 1, 1}, {1, 10, 15, 6}) --cube of max ideal
({3, 1, 2}, {1, 8, 9, 2}) -- 8 general cubics
({3, 1, 3}, {1, 7, 7, 1}) -- Pfaffian
({3, 2, 1}, {1, 5, 9, 5}) -- 5 generic cubics
({3, 2, 3}, {1, 4, 4, 1}) -- doesn't exist, but the double does (testGeneric(D,2))

({4, 1, 1}, {1, 15, 24, 10}) -- 4th power of max ideal
({4, 1, 4}, {1, 9, 9, 1}) -- Pfaffian
({4, 2, 1}, {1, 7, 14, 8}) -- 7 general 4-ics or testGeneric

({4, 5, 1}, {1, 3, 8, 6})  --- does NOT exist (would be reg seq). 
-- over a field with 2,3, or 5 elements, 2 times this is ok

({5, 1, 1}, {1, 21, 35, 15}) -- 5th power of max ideal
({5, 1, 2}, {1, 16, 20, 5}) -- 16 general qpuintics OR testGeneric
({5, 1, 5}, {1, 11, 11, 1}) -- Pfaffian
({5, 2, 5}, {1, 6, 6, 1})   -- doesn't exist, but double does from testGeneric
({5, 3, 1}, {1, 6, 15, 10}) -- generic forms

({6, 1, 1}, {1, 28, 48, 21}) -- 6th power of max ideal
({6, 1, 2}, {1, 21, 27, 7}) -- generic forms
({6, 1, 6}, {1, 13, 13, 1}) -- Pfaffian
({6, 2, 1}, {1, 12, 27, 16}) -- generic forms

({7, 1, 1}, {1, 36, 63, 28}) -- power of max id
({7, 1, 7}, {1, 15, 15, 1})  -- pfaffian
({7, 2, 1}, {1, 15, 35, 21}) -- generic forms
({7, 2, 7}, {1, 8, 8, 1})   -- doesn't exist, but twice it does (testGeneric)
({7, 3, 2}, {1, 8, 14, 7}) -- generic forms

({8, 1, 1}, {1, 45, 80, 36}) -- power of the max ideal
o({8, 1, 2}, {1, 33, 44, 12}) -- generic forms
({8, 1, 3}, {1, 27, 32, 6})  -- generic forms
({8, 1, 8}, {1, 17, 17, 1})  -- Pfaffian
({8, 3, 1}, {1, 11, 32, 22}) -- generic forms
({8, 6, 1}, {1, 5, 20, 16}) -- testSocle

({9, 1, 1}, {1, 55, 99, 45})-- power of the max ideal
({9, 1, 2}, {1, 40, 54, 15}) -- generic forms
({9, 1, 5}, {1, 25, 27, 3}) -- testSocle
({9, 1, 9}, {1, 19, 19, 1}) -- Pfaffian
({9, 2, 1}, {1, 22, 54, 33}) --generic
({9, 2, 9}, {1, 10, 10, 1}) --testSocle 2
({9, 3, 1}, {1, 13, 39, 27}) -- generic (not testSocle)
({9, 5, 1}, {1, 7, 27, 21}) -- testSocle

({10, 1, 1}, {1, 66, 120, 55})-- power of the max ideal
({10, 1, 10}, {1, 21, 21, 1}) -- Pfaffian
({10, 2, 1}, {1, 26, 65, 40}) -- generic
({10, 2, 3}, {1, 18, 25, 8})  -- generic (not socle)
({10, 3, 2}, {1, 13, 25, 13}) -- socle
({10, 5, 1}, {1, 8, 32, 25})  -- socle


The following are all the examples in 
3 variables up to deg shift 
E=(20, 20, 20) where neither of the
obvious construction methods works.
We know the 1,2n,2n,1 are impossible,
but become possible when doubled. (proof??)


--the symmetric cases with even # gens
({1, 2, 1}, {1, 2, 2, 1})
({3, 2, 3}, {1, 4, 4, 1})
({5, 2, 5}, {1, 6, 6, 1})
({7, 2, 7}, {1, 8, 8, 1})
({9, 2, 9}, {1, 10, 10, 1})
({11, 2, 11}, {1, 12, 12, 1})
({13, 2, 13}, {1, 14, 14, 1})
({15, 2, 15}, {1, 16, 16, 1})
({17, 2, 17}, {1, 18, 18, 1})
({19, 2, 19}, {1, 20, 20, 1})

load "BoijSoderberg.m2"

Weyman(0,11,13,24)
bettiH pureBettiDiagram(0,11,13,24)

--the cases I don't understand yet:
({4, 5, 1}, {1, 3, 8, 6}) -- -- over a field with 2,3, or 5 elements, 2 times this is ok. Weyman give 15
({6, 14, 1}, {1, 2, 9, 8}) --Weyman gives 105. Twice this cannot exist -- would be Buchsbaum-Rim. But
--3 times it does, over fields of 2,3,5 elements (testGenerators)
({15, 20, 1}, {1, 3, 27, 25}) -- Weyman gives 210
--mu=1 can't exist, but mu=2 does (testGenerators) over fields of 2,3,5 elements

--I still can't  construct the following two in "small" examples!
({17, 4, 3}, {1, 18, 34, 17}) --Weyman = 42 -- so far, unable to construct a small one!
({18, 7, 3}, {1, 10, 24, 15}) --Weyman = 105 -- similarly here.
--It doesn't see obvious why these shouldn't  exist, even with mu=1.
WeymanE=E->Weyman({0}|accumulate(plus, {0}|E))
WeymanE{18,7,3}

test= E->(
D={0}|accumulate(plus, {0}|E);
L=pureBetti D;
S=kk[a,b,c];
print (B=testGenerators(D,1));
print isPure B;
--betti res ideal random(S^2,S^{2*L_1:-E_0});
print (B1=testSocle(D,1));
isPure B1)
--print testSocle(D,2))

restart
load "BoijSoderberg.m2"

kk=ZZ/17
--E={1,2,1} -- just to make sure it's working
--E={6,14,1} -- testGenerators finds one with mu = 3
--E={15,20,1} -- testGenerators with mu=2
--E={17,4,3} -- over 100 testGenerators tries in char 2 with each of 1,2,3 gens failed.
--also tries with testSocle and mu = 1 and 2 (this is slow, seems to have a mem leak.)
E={18,7,3} -- 1000 runs of testGens with mu=1 and
E={3,7,18}
-- 100 runs of testGens with mu=2 in char 2 gave nothing 
D={0}|accumulate(plus, {0}|E);
B= bettiH pureBettiDiagram D
mu=1
time for i from 1 to 1000 do (
     if i%100==0 then print i;
     if mu*B==testGenerators(D,mu) then ( print M; print i; break))
betti res coker M

kk=ZZ/2
time for i from 1 to 3 do (
     if i%100==0 then print i;
     print testGenerators(D,mu))

betti res coker M

time for i from 1 to 1000 do (
     if i%10==0 then print i;
     if mu*B==testSocle (D,mu) then ( print M; break))


restart
load "BoijSoderberg.m2"
kk=ZZ/2
d=3
D={0,d,d+2,2*d+2}
testSocle(D,2)
M=prune M
FF=res M
phi=presentation M
phi1=transpose (FF.dd_3)**(ring M)^{-8}
betti phi
betti phi1
betti prune Hom(coker phi, coker phi1)
--NOT iso.

testSocle(D,3)
testGenerators(D,2)

load "LexIdeals.m2"

load "BoijSoderberg.m2"
pureBetti(L1={0,3,5,6,14,15})
pureBetti(L2={0,3,5,7,14,15})
pureBetti(L3={0,3,6,7,14,15})

product L1_{1..5}/5!
L1
length L1
pureBetti{0,3,4,6}
pureBetti{0,3,5,6}
pureBetti{0,4,5,6}

pureBetti{0,1,2,4,5}
pureBetti{0,2,3,4,5}

pureHilb = L->(
B:=pureBetti L;
n:=length L -1;
LL=for i from 0 to 10 list --max L-n+1 list
     sum(for j from 0 to n when L_j<=i list (-1)^j*binomial(n-1+i-L_j, n-1)*B_j);
LL)--/(sum LL))

pureHilb{0,2,3,6}-pureHilb{0,2,4,6}
pureHilb{0,2,4,6}-pureHilb{0,3,4,6}

pureHilb{0,2,3,7}-pureHilb{0,2,4,7}
pureHilb{0,2,4,7}-pureHilb{0,3,4,7}
pureHilb{0,3,4,7}-pureHilb{0,3,5,7}
pureHilb{0,3,5,7}-pureHilb{0,4,5,7}
pureHilb{0,4,5,7}-pureHilb{0,4,6,7}

pureBetti{0,1,2,6}
pureBetti{0,1,3,6}
pureBetti{0,2,3,6}

pureBetti{0,1,3,5}
pureBetti{0,1,2,5}

testSocle({0,2,3,6},1)

---

pureBetti{0,1,2,5,6,7}
pureHilb{0,1,2,6,7,8}
pureBetti{0,1,2,4,7,8}

pureBetti{0,1,2,3,6,7}
pureBetti{0,2,3,4,7,8}
112*5-9*70
pb=L->pureBetti L
pb{0,1,2,3,4,7}
126*5-9*105
oo/9
pb{0,1,3,4,7,8}
15*14+5*84-9*78

----------------
restart
load "BoijSoderberg.m2"
P0=matrix"1,0,0,0;
       0,3,0,0;
       0,1,6,3"
B0=mat2betti P0
decomposeAll B0

P1=matrix"1,0,0,0;
       0,3,2,0;
       0,3,6,3"
B1=mat2betti P1
HilbList decomposeAll B0
HilbList decomposeAll B1

HilbList= L-> for i from 0 to #L-1 list(if i%2==0 then L_i else hashTable2Hilb L_i) 

-------------------
restart
load "BoijSoderberg.m2"
S=kk[a,b]
B=betti res ideal"a2,ab"
decomposeAll B
facetEquation({0,2,3},1,1)

----------
restart
load "BoijSoderberg.m2"
F=facetEquation({0,2,3,7},1,-3,4)
S=kk[a,b,c]
0_S
catalecticantAdjoint=(S,a)->(
     map(S^a, S^{a+2:-1}, (i,j)->if j==i then S_0 else if j==i+1 then S_1 else if j==i+2 then S_2 else 0_S)
     )
ca=(S,a)->catalecticantAdjoint(S,a)
m=ca(S,6)
     
FF=res coker m
betti FF
hf(0..5,coker m)
-----------
restart
load "BoijSoderberg.m2"
F=facetEquation({0,1,3,5},0,-3,6)
F=facetEquation({0,1,3,6},0,-3,6)
F=facetEquation({0,1,3,7},0,-3,6)
F=facetEquation({0,1,3,8},0,-3,6)
F=facetEquation({0,1,3,9},0,-3,6)
F=facetEquation({0,1,3,10},0,0,8)
numericalComplex F

F=facetEquation({0,1,4,6},0,-3,10)
F=facetEquation({0,1,3,6},0,-3,6)
F=facetEquation({0,1,3,7},0,-3,6)
F=facetEquation({0,1,3,8},0,-3,6)
F=facetEquation({0,1,3,9},0,-3,6)
F=facetEquation({0,1,3,10},0,-3,8)

F=facetEquation({0,1,3,4},0,-3,6)

F=facetEquation({0,1,3,4,5,6},0,-3,6)

F=facetEquation({0,1,3,5},0,-8,6)
F=facetEquation({0,1,3,4,6},0,-3,6)
F=facetEquation({0,1,3,4,5,7},0,-3,7)

F=facetEquation({0,1,5,8},0,-8,5)


S=kk[a,b,c]
P=ker map(S^1, S^{2:-1,-2},matrix"a,b,c2")
P=prune P
hf(0..10, P)

P=coker map(S^2, S^{-1}, matrix"a;b")
hf(0..5, P)
prune Hom(P, S^1)

N=coker random(S^3, S^{5:-1})
NN= res N	  
NN.dd
P=coker NN.dd_3
hf(0..10, P)	  


N=coker random(S^5, S^{7:-1})
NN= res N	  
NN.dd
P=coker NN.dd_3
hf(0..10, P)	  
hf(0..10, N)
facetEquation({0,1,4,10},0,-8,8)


facetEquation({0,1,3,8},0,-8,8)
N=coker random(S^2, S^{3:-1,-3})
hf(0..6, N) 
betti (NN=res N)
Q=ker(NN.dd_1)
hf(0..8, Q)
hf(0..8, S^{-3})

restart
load"BoijSoderberg.m2"

for u from 2 to 7 do
     (print("----",0,1,4,4+u);
     print facetEquation({0,1,4,4+u},0,-3,1+u))


restart
load"BoijSoderberg.m2"

kk=ZZ/32003
S=kk[x_1..x_3]
F=res (S^1/ideal(x_1^2, x_2^3, x_3^4))
E=Hom(chainComplex(transpose F.dd_2, transpose F.dd_1), S^1)
--E should be a complex going from homological degree 0 to a negative homological degree.
betti E
betti E1

time for i from -5 to 20 do
print supportFunctional(E**S^{i},E1)

time for i from -5 to 20 do
print supportFunctional(E**S^{i},betti E1)

a=3
E1=res (coker random(S^a, S^{a+2:-1}), LengthLimit=>2)
E=Hom(chainComplex(transpose E1.dd_2, transpose E1.dd_1), S^1)
d3=8
for i from -5 to 15 do
print supportFunctional(E**S^{i}, bettiH pureBettiDiagram randomDegreeSequence(3,5))
for i from -5 to 15 do
print supportFunctional(E**S^{i}, bettiH pureBettiDiagram(0,2,d3-a-1,d3))

facetEquation({0,3,5,6},2,-3,4)
facetEquation({0,1,3},0,-2,2)
L=facetEquation({5,7,10,11},2,-1,10)
numericalComplex L
F=facetEquation({0,1,4,7},0,-5,5)
numericalComplex F

--------
restart
load "BoijSoderberg.m2"
L={0,0,0}
for u from 0 to 6 do
print Bott(L,u)
L={5,2,1,1}
for u from 0 to 10 do
Bott({0,0},-1)
print Bott(L,-u)
Bott({3,2,1},-10,0)
Bott({0,0,0},-5,5)
------------

restart
load "BoijSoderberg.m2"
load "randomIdeal.m2"
d={0,3,4,6,7,8}
F=facetEquation(d,1,0,4)


I=ideal(x_0,x_1)*ideal vars S
B=betti res I
dotProduct(F,0,B)

d=randomDegs(5,4,3)
S
F=facetEquation(d,3,0,4*5)
S
S=kk[x_0..x_4]
vars S

B=toList ((ideal(vars S))^3)
i=randomSparseIdeal(B,2,5)

---
M=map(ZZ^{{}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}}, ZZ^{{},
	  {}, {}, {}, {}}, {{0, 20, -28, 27, -20}, {0, 28, -27, 20, -10}, {0, 27,
	       -20, 10, 0}, {0, 0, 0, 0, 7}, {0, 0, 0, 0, 8}, {0, 0, 0, 0, 0}, {0, 0,
	       0, 0, 0}, {0, 0, 0, 0, 0}, {0, 0, 0, 0, 0}, {0, 0, 0, 0, 0}, {0, 0, 0,
	       0, 0}, {0, 0, 0, 0, 0}, {0, 0, 0, 0, 0}})  
B=new BettiTally from {(3,{16},16) => 8, (4,{16},16) => 9, (4,{17},17)
     => 6, (2,{12},12) => 1, (2,{13},13) => 32, (2,{14},14) => 8, (3,{14},14)
     => 28, (0,{0},0) => 1, (2,{15},15) => 1, (1,{8},8) => 7, (3,{15},15) =>
     16, (4,{15},15) => 1}
dotProduct(M,0,B)

---
restart
load "BoijSoderberg.m2"
--genus 7 canonical curves
kk=ZZ/32003
kk=ZZ/2
g=7
S=kk[vars(0..g-3)]
s=random(S^1, S^{-3})
i= ideal fromDual s
B=betti res i
decomposeAll B
L={0,2,3,5,6,8}
testSocle(L,2)

----------------------
restart
load "BoijSoderberg.m2"
kk=ZZ/32003

dseq=(a,b)->if b>0 
then toList join(0..a-1, a+1..a+b) else toList(0..a-1)
dseq(4,0)
dseq(1,3)
facetEquation(dseq(2,2), 0, -1, 3)
facetEquation(dseq(3,1), 1, -5, 3)
facetEquation(dseq(4,0), 2, -1, 3)

fe=n->(
     for a from 2 to n+1 list(
	  b=n+1-a;
     	  facetEquation (dseq(a,b),a-2, 0,1))
)
bd=n->(for a from 1 to n list
bettiH pureBettiDiagram dseq(a,n+1-a)
)

fe 3
bd 3

fe 4
bd 4

fe 5
bd 5

fe 2
fe 3
fe 4
fe 5
factor (2^12 -1)

----------------------
load "BoijSoderberg.m2"
kk=ZZ/32003
d={0,2,3,5,6,8}
pureBetti d
d={0,2,3,4,6,8}
bettiH (pureBettiDiagram d)
S=kk[x_0..x_4]
f=sum toList apply (x_0..x_4, i->i^3)

kk=ZZ/3
S=kk[x_0..x_4]
r=0
tally for i from 1 to 1000 list(
f=random(S^1,S^{-3});
m=fromDual matrix{{f}};
B=betti (F=res coker m);
r=rank F_3;
--if r> 26 print B;
B)
viewHelp tally

kk=ZZ/2
S=kk[x_0..x_4]
r=0
f=random(S^1,S^{-3});
m=fromDual matrix{{f}};
B=betti (F=res coker m)
decomposeAll B

---------------------------
---------Tate Resolutions--
--------------------------

restart
load "BoijSoderberg.m2"

Z={4,2,0,-3} -- list, strictly decreasing

Z={0}
pureTate(Z, -6, 6)

Z={2,0}
pureTate(Z, -6, 6)

Z={2,0, -3}
pureTate(Z, -6, 6)
Z={2,-1, -3}
pureTate(Z, -6, 6)
Z={2,-2, -3}
pureTate(Z, -6, 6)
-----------------------

restart
load "BoijSoderberg.m2"

Z={5,4,2,0,-2,-5,-6}	  
pureTate(Z,-6,6)
pureTate(Zplus(Z,4),-6,6)
pureTate(Zminus(Z,4),-6,6)
d=degreeSequence(Z,4)
bettiMatrix(d,-6,6)
facetTate(Z,4,-6,6)	  
1848/1650==28/25

Z={5,4,2,0,-2,-5,-6}	  
pureTate(Z,-6,6)
pureTate(Zplus(Z,3),-6,6)
pureTate(Zminus(Z,3),-6,6)
d=degreeSequence(Z,3)
bettiMatrix(d,-6,6)
facetTate(Z,3,-6,6)	  
8316/6600==63/50

Z={1,-2}
facetTate(Z,0,-4,4)
Z={2,-2}
facetTate(Z,0,-4,4)

restart
load "BoijSoderberg.m2"

Z={4,0,-3}
facetTate(Z,1,-4,5)
d=degreeSequence(Z,1)
bettiMatrix(d,-5,0)

--right boundary
Z={4,0,-3}
facetTate(Z,0,-4,5)
d=degreeSequence(Z,0)
bettiMatrix(d,-5,0)

--left boundary
Z={4,0,-3}
facetTate(Z,2,-4,5)
d=degreeSequence(Z,2)
bettiMatrix(d,-5,0)


Z={0}
facetTate(Z,0,-4,5)
d=degreeSequence(Z,0)
bettiMatrix(d,-5,0)


--------------------

Z={0,-4,-7}
-------What does the following code do?? Gives weird output.
--ZtoD=(Z,t)->(
--for i from 0 to #Z+1 list (
--     i-> if i<t or i>t then -Z_i else 
--     if i=t then {-(Z_i)-1, -(Z_i), -(Z_i)+1}))

-------------------
--Test the formula for the facets of vector bundles:
restart
load "BoijSoderberg.m2"
Z={0,-4,-7}
facetFormula(Z,1,-10,10)
facetTate(Z,1,-10,10)
facetFormula(Z,0,-10,10)
facetTate(Z,0,-10,10)
facetFormula(Z,2,-10,10)
facetTate(Z,2,-10,10)

Z={4,3,1,-2,-7}
facetFormula(Z,3,-10,10)
facetTate(Z,3,-10,10)

bettiH pureBettiDiagram{0,2,3,4,6,8}
m=matrix"1,0,0,0,0,0;
       0,10,16,12,0,0;
       0,0,12,16,10,0;
       0,0,0,0,0,1"

x=9
m=matrix"1,0,0,0,0,0;
       0,10,16,x,0,0;
       0,0,x,16,10,0;
       0,0,0,0,0,1"
B=mat2betti m
decomposeAll B

-------------
restart
load "BoijSoderberg.m2"

Lupper=  {0,2,4,5,6,8}
Lmiddle= {0,2,3,5,6,8}
Llower=  {0,2,3,4,6,8}
bettiH pureBettiDiagram Lupper
bettiH pureBettiDiagram Lmiddle
bettiH pureBettiDiagram Llower
facetEquation (Llower,2,-4,4)


bettiH pureBettiDiagram {0,2,3,6,8}
Weyman {0,2,3,6,8}
---
facetEquation({0,1,2,4},1,-4,1)


facetEquation({0,1,3,4},0,-4,1)
facetEquation({0,2,3,5},1,-4,3)
facetEquation({0,1,3,4},2,-4,3)
facetEquation({0,1,2,4,6},1,-4,4)
facetEquation({0,1,2,4},1,-4,1)
facetEquation({0,1,2,5},1,-4,4)
facetEquation({0,1,2,3},2,-4,4)


restart
load "BoijSoderberg.m2"

Lupper=  {0,2,4,5,6,8}
Lmiddle= {0,2,3,5,6,8}
Llower=  {0,2,3,4,6,8}
bettiH pureBettiDiagram Lupper
bettiH pureBettiDiagram Lmiddle
bettiH pureBettiDiagram Llower
facetEquation (Llower,2,-4,4)

restart
load "BoijSoderberg.m2"
--Three consecutive degree sequences that give the simplest non-trivial
--facet in the Boij-Soederberg cone of resolutions in 3 variables, and their
--betti tables:

bettiH pureBettiDiagram {0,2,3,4}
bettiH pureBettiDiagram {0,1,3,4}
bettiH pureBettiDiagram (Llower=  {0,1,2,4})

--The facet equation:

facetEquation (Llower,1,-7,1)

--An explanation for the numbers in the table:
--They are Hilbert functions of cohomology of a free complex.
S=ZZ[x,y,z]
m=random(S^3, S^{5:-1})
apply(-1..3, i->hilbertFunction(i, coker m))
apply(3..10, i->hilbertFunction(i, ker m))


