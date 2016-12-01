--Testing the Boij-Soderberg Conjecture.

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
--bin  -- binomial coeff
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
--Most important routines:

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

--testSocle
--takes a degree sequence and produces the generic module with same
--socle and generator type of a module that would have the minimal possible
--pure resolution with that degree sequence. (this module does NOT in general
--have a pure resolution!)

--testGenerators 
--does the same thing, but with random choices of the right number of generators in the right
--degree.

--pureHilb
--takes list of degrees, computes the hilbert function of the module with 
--corresponding pure resolution


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

--rank of a Schur functor on a module
--input: a non-neg integer n and a non-increasing sequence of non-neg integers L
--output: the rank of the representation S_L(C^n). Here (11111) represents an exterior power, (k) a symmetrci power.
rkSchur = (n,L)->(
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
     D:=for i from 1 to #L-1 list L_i-L_0;
     E0:=for i from 1 to #D-1 list  D_(i)-D_(i-1)-1;
     E:={D_0-1}|E0;
     Eplus1:=E+toList(#D:1);
     lambda := for i from 1 to #D list sum E_{i..#D-1};
     A:={lambda}|for i from 0 to #D-1 list(
	  lambda+ (Eplus1_{0..i}|toList(#D-1-i:0)));
     apply(A, a->rkSchur(#D,a))
     )
///
load "BoijSoderberg.m2"
Weyman(0,1,2,3,4)
Weyman(0,1,3,4)
W=Weyman {0,4,6,9,11}
P=pureBetti(0,4,6,9,11)
for i from 0 to #W-1 list (W_i/P_i)
///

--take a betti table or hash table to the sequence of degrees in its lowest row.

--Input: a hash table or BettiTally
--Output: the lenght of the free resolution it represents.
projectiveDimension = B -> max apply ((keys B), i->i_0)

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
--output true or false depending on whether the list is strictly increasing.
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
peek B
#B
length keys B
max ((keys B)/first)

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


---------------------------Now routines from Frank Schreyer, revised a little and with 
---------------------------a new "facetEquation"


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

rangeOK(List,ZZ,ZZ):=(d,r,n)->#d==n+1 and 0<= d_0 and 
   apply(n,i-> d_i<d_(i+1))==toList(n:true) and d_n<=r+n 
   --tests whether degree seq is non-neg, strictly increasing, of the right length n, and last elt
   -- is bounded by reg + num vars, and 

rangeOK(List,ZZ,ZZ,ZZ):=(d,lowestDegree, highestDegree, n)->
#d==n+1 and lowestDegree<= d_0 and apply(n,i-> d_i<d_(i+1))==toList(n:true) and d_n<=highestDegree+n 
   --tests whether degree seq is >=lowestDegree, strictly increasing, of the right length n, and last elt
   -- is bounded by highestDegree + num vars.

bettiMatrix=method()
bettiMatrix(List):=d->(
     --betti matrix of a pure complex from list of degs
     if  rangeOK(d,r,n) then (
     bb:=bettiNumbers(d);
     matrix apply(r+1,i->apply(n+1,j->if (d_j)==i+j then bb_(0,j) else 0))
     ) else error( "wrong Range"))

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
bettiMatrix(d,-1,0)
///
nextLower=method()
nextLower(List):=d->(if d_0>0 then join( {d_0-1},d_{1..n}) else (
	  --returns A deg seq adjacent to d and below it (chooses one such)
	  k:=1; 
	  while (d_k-1==d_(k-1)) do (k=k+1);
	  join(d_{0..k-1},{d_k-1},d_{k+1..n})))
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
nextUpper(List):=(d)->(if d_n<n+r then join(d_{0..n-1},{d_n+1}) else (
	  --same but above
	  k:=n; 
	  while (d_k-1==d_(k-1) ) do (k=k-1);
	  join(d_{0..k-2},{d_(k-1)+1},d_{k..n})))
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

lowerRange(List):=(d)->(
	  --returns a maximal chain of deg seqs below d
	  A:={d};
	  if d =!= toList(0..n)  then (
          e:=nextLower(d);
	  A=join(A,lowerRange(e)));
     	  A)
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

upperRange(List):=(d)->(
          --same but above
	   A:={d};
	   if d =!= toList(r..n+r) then ( 
          e:=nextUpper(d);
	  A=join(A,upperRange(e)));
     	  A)
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
rangeMatrices(List):=(e)->apply(n+1,k-> matrix apply(r+1,i->apply(n+1,j->
	       --takes a deg seq, returns list of mats, i-th has 
	       --a one in posn e_i-i, i
	       if  k==j and e_k==i+j then 1 else 0)))

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

numericalComplex=A->(AA:=A;apply(n+r+1,i->(
	       PS:=peskineSzpiro(r,n); 
	       ss:=if i<=r then AA_(r-i,n) else AA_(0,n-i+r);
	       AA=AA-ss*PS_i;
	       ss)))
--The numerical complex that flips the "upper" eqn to the "lower" eqn, written
--as the sequence of coefficients of the PS-equations.

flipEquation=(A)->(aa:=numericalComplex(A);
     PS:=peskineSzpiro(r,n); 
     apply(n+r+1,c->A-sum(c,i->aa_(i)*PS_(i))))
upperEquation=(A)->(L:=flipEquation(A);L_(#L-1))
--the necessary lin comb of the PS equations.

middleComplex=(d,e)->(
     n=#d-1;
     t:=1;
     L:=apply(n+1,i->(t=t*if d_i==e_i then 1 else -1 ));
     apply(n+1,c->if L_c==1 then e_c else d_c))

nextPure=(d,k)->if d_k+1==d_(k+1) and (k==#d-2 or d_(k+2)>d_(k+1)+1) then 
     apply(#d,i->if i<k or i>( k+1) then d_i else d_i+1) else error("no next pure sequence")
--in the case of two degree sequences differing by one in two consec places, computes
--the degree sequence in between.

twoRowPureComplex=(d0,k,reg)->apply(n+1,i->if i<k then d0+i else d0+i+reg-1)
--deg sequence of a two-row pure resolution
--with generator in degree d0, k>=2 position of the step, reg=regularity-d0

twoRowFacet=(d0,k,reg)->(
     --returns the facet equation and other info for the facet corresponding to an
     --upper complex with degrees as produced by twoRowPureComplex
     d:=twoRowPureComplex(d0,k,reg);
     e:=nextPure(d,k-2);
     de:=middleComplex(d,e);
     R:=sum(rangeMatrices(e))+sum(rangeMatrices(d))+sum(rangeMatrices(de));
     A:=supportingEquation(d,e);
     ss:=numericalComplex(A);
     Aminus:=upperEquation(A);
     (A,R,ss,Aminus))

threeRowFacet=(d0,k,steps)->(
     --similar for a "three-row complex" (one "elevator", ie
     --------
     	     --
	     --
	       
	       ------------)
     --generator in degree d0, 1<k position of the step, 
     --0<=step_0,1<=step_1 step size)
     d:=apply(n+1,i->if i<k then d0+i else if i<k+2 then d0+i+steps_0 else d0+i+steps_0+steps_1);
     e:=nextPure(d,k);
     de:=middleComplex(d,e);
     R:=sum(rangeMatrices(e))+sum(rangeMatrices(d))+sum(rangeMatrices(de));
     A:=supportingEquation(d,e);
     ss:=numericalComplex(A);
     Aminus:=upperEquation(A);
     (A,R,ss,Aminus))

supportingEquation=method();
supportingEquation(List,List):=(d,e)->(
     --given degree sequences d < e, with e-d has ones in two consecutive places (the box),
     --computes the supporting equation of the exterior facets involving this edge.
     A:=matrix apply(lowerRange(d),c->join(toSequence entries bettiMatrix(c)));
     B:=matrix apply(upperRange(e),c->join(toSequence entries bettiMatrix(c)));
     C:=matrix apply(rangeMatrices(e),c->join(toSequence entries c));
     D:=(entries transpose syz(A||B||C))_0;
     A=matrix apply(r+1,i->apply(n+1,j->D_((n+1)*i+j)));
     de:=middleComplex(d,e);
     B=bettiMatrix(de);
     if dotProduct(A,B)>0 then A else -A)

supportingEquation(List,List,ZZ,ZZ):=(d,e,lowest,highest)->(
     --lowest should be <=d_0, highest-lowest >=e_n-n, where n=#d-1.
     --given degree sequences d < e, with e-d has ones in two consecutive places (the box),
     --computes the supporting equation of the exterior facets involving this edge.
     --this version outputs matrix with highest-lowest+1 rows, starting from
     --degree lowest and going to degree highest.
     n=#d-1;
     r=highest-lowest;
     dplus:=d/(X->X-lowest);
     eplus:=e/(X->X-lowest);
     A:=matrix apply(lowerRange(dplus),c->join(toSequence entries bettiMatrix(c)));
     B:=matrix apply(upperRange(eplus),c->join(toSequence entries bettiMatrix(c)));
     C:=matrix apply(rangeMatrices(eplus),c->join(toSequence entries c));
     D:=(entries transpose syz(A||B||C))_0;
     A=matrix apply(r+1,i->apply(n+1,j->D_((n+1)*i+j)));
     de:=middleComplex(dplus,eplus);
     B=bettiMatrix(de);
     if dotProduct(A,B)>0 then A else -A)


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

--facetEquation(List,ZZ,ZZ):=(d,i,extraRows)->(
--     --i an integer between 0 and #d-2
--     --d a strictly increasing list of integers 
--     --such that d_(i+1)=d_i+1
--     --extraRows a positive integer --- actually the negative of the degree
--     --in which the equation matrix begins.
----routine produces the "upper" equation of the supporting hyperplane
----of the facet corresponding to d< (...d_i+1, d_(i+1)+1,...)=nextpure(d,k).
----the equation is presented as a 
---- map ZZ^{0..#d-1} --> ZZ^{-extraRows..d-n}
----beginning on the line -extraRows.
--n=#d-1;
--dplus:=for i from 0 to #d-1 list d_i-d_0+extraRows;
--r:=if i==#d-2 then max dplus-n+1 else max dplus-n;
--e:=nextPure (dplus,i);
--supportingEquation(dplus,e)
----map(ZZ^{-extraRows..#d-n}, ZZ^{0..#d-1}, 
--)
facetEquationOLD=method()
facetEquationOLD(List,ZZ,ZZ,ZZ):=(d,i,lowestDegree, highestDegree)->(
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
     n=#d-1;
     r=highestDegree-lowestDegree;
     dplus:=d/(X->X-lowestDegree);
     e:=nextPure(d,i);
     eplus:=e/(X->X-lowestDegree);
     A:=matrix apply(lowerRange(dplus),
	  c->join(toSequence entries bettiMatrix(c)));
     B:=matrix apply(upperRange(eplus, c->join(toSequence entries bettiMatrix(c)));
     C:=matrix apply(rangeMatrices(eplus),c->join(toSequence entries c));
     D:=(entries transpose syz(A||B||C))_0;
     A=matrix apply(r+1,i->apply(n+1,j->D_((n+1)*i+j)));
     de:=middleComplex(dplus,eplus);
     B=bettiMatrix(de);
     if dotProduct(A,B)>0 then A else -A))
--supportingEquation(d,nextPure(d,i),lowestDegree, highestDegree))

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

--input: E is a hash table with entries
--firstE is an integer specifying the "degree" of the first row of E
--(so if E=facetEquation(d,j,m), the the first row of E should be degree d_0-m).
--B is a Betti Table
-- beta_(i,j). 
--returns error if the betti table doesn't "fit inside"
--the matrix, else returns the dot product
--\sum E_(i,j)*beta_(i,j).
///

--BB=betti2matrix B;
--if BB_1 < -firstrow or BB_1+rank target BB_0 > firstrow+rank target E, then error "betti matrix doesn't fit"
--     else sum(keys B, BB_(last k - first k, first k)*E_(last k - first k, first k)
--     dotProduct(E,betti2matrix betti F, firstrow)
--needs to be fixed.
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

end

----------------------------------

restart
load "BoijSoderberg.m2"
d={0,1,2,4,5}
facetEquation(d,1,10)
facetEquation(d,3,10)
pureBetti{0,1,4,5}
pureBetti{0,1,5,6,7}

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


code fromDual
vars S

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
F=facetEquation({0,1,3,10},0,-3,8)

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

facetEquation({0,3,5,6},2,-3,3) -- Nov 5: this crashes.
facetEquation({0,1,3},0,-2,2)
L=facetEquation({5,7,10,11},2,-1,10)
numericalComplex L
