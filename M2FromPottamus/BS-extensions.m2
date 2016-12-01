needsPackage "BGG"

dim(CohomologyTally) := ZZ => D ->max apply (keys D, first)

topZeroSequence =method()
topZeroSequence(CohomologyTally):= C -> (
	  lowColumnNumber:=min apply (keys C,k-> k#0+k#1);
       	  highColumnNumber:=max apply (keys C,k-> k#0+k#1);
          topPositions := for i from lowColumnNumber to highColumnNumber list (
	  B1 := select(keys C, k -> k#0+k#1 == i);
	  {i,max apply(B1, k-> k_0)});
          tp:=apply(topPositions, t->t#0-t#1);
	  sort toList difference(set(min tp..max tp), set tp)
     )

topSupernaturalPart =method()
topSupernaturalPart(CohomologyTally):= C -> (
	  lowColumnNumber:=min apply (keys C,k-> k#0+k#1);
       	  highColumnNumber:=max apply (keys C,k-> k#0+k#1);
          zeros:=topZeroSequence C;
	  pC:=pureCohomologyTable(zeros,  lowColumnNumber,highColumnNumber);
	  multiplier:=min apply(keys pC, k-> C_k/pC_k);
	  (multiplier, pC)
     )

QQ * CohomologyTally := (d,C) -> applyValues(C, v -> d*v)

rank(CohomologyTally):= C->(
    d:=dim C;
    lowTwist:=min apply (keys C,k-> k#0+k#1);
    highTwist:=max apply (keys C,k-> k#0+k#1-d);
    if highTwist-lowTwist < d then error("not enough columns in table");
    chi:=for i from lowTwist to lowTwist+d list (sum(0..d, j->(-1)^j*C_(j,i)));
    (-1)^d*sum (0..d, i->(-1)^i* binomial(d,i)*chi_i)
    )     

normalizedMultipliers = C->(
     C2:=C;
     d=dim C;
     while dim C2==d list(
	  (C1:=topSupernaturalPart C2; print topZeroSequence C2;print"-----------------";
	   C2=C2-(first C1 * last C1); 
	   rank(last C1)*first C1)))

zeroSequences = C ->(
     C2:=C;
     d=dim C;
     while dim C2==d do(
	  C1:=topSupernaturalPart C2; 
	  if first C1 <=0 then (
	       print C2;
	       error ("non-positive multiplier encountered"));
	  print topZeroSequence C2;
--	  print "-----------------";
	   C2=C2-(first C1 * last C1); 
	   if not isPositive C2 then (
		print C2;
		error("negative entry found")
	  ));
     C2)

nextZeroSequence = C ->(
     C2:=C;
     d=dim C;
	  C1:=topSupernaturalPart C2; 
	  if first C1 <0 then error ("negative multiplier encountered");
	  print topZeroSequence C2;
--	  print "-----------------";
	   C2=C2-(first C1 * last C1); 
	   if not isPositive C2 then (
		print C2;
		error("negative entry found")
	  );
     C2)

isPositive = C->(
     --check whether the entries of C are all non-negative
     if any (values C, v->v<0) then false else true)

addToTable=(C,i,d,n)->(
     --Adds n to the entry representing the H^i(E(d)), the i-th cohomology
     --of the d-th twist.
     D:=new MutableHashTable from C;
     if D#?(i,d) then (
	  if (D#(i,d)+n==0) then remove(D,(i,d))
	  else D#(i,d)=D#(i,d)+n)
     else (D#(i,d)=n;
	  if D#(i,d)<0 then print "warning: new entry is negative"
	  );
     new CohomologyTally from D)

--The next routines implement the functionals
--$\chi_d^{\leq j}$ and L of our paper on coho
--tables of coherent sheaves.

--This is $\chi_d^{\leq j}$. Note that the keys come in the 
--order "coho degree, twist", the opposite of this function.

partialEuler = (d,j,C) ->(
     sum(j+1, i->(if not C#?(i,d) then 0 else
	       (-1)^i*C#(i,d))))

sigma = method()
sigma(ZZ,ZZ) := (s,j) -> (
     --produce the list of indices for the L functional.
     --if 
     for i from 0 to s+1 list (
	  if i<= j-1 then i else
	  if i== j then i-1 else
	  if i> j then i-2))
sigma(ZZ) := s -> sigma(s,s+2)

rList = L -> (
     for i from 0 to #L-1 list (
	  product(
	       flatten(
		    for j from 0 to #L-2 list (
			 if j==i then {1} else  
		         for k from j+1 to #L-1 list 
		              if k==i then 1 else L_k-L_j
		    	      )
	       	    	 )
	       	    )
     	       )
     	  )
///
restart
load "BS-extensions.m2"
rList {0,1,2,5}
		    for j from 0 to 5 when j=!=2 list j
///
LL = method()

LLTest=(L,C)->(
-- should be identically 0
--as soon as the list L contains at least dim C +2 integers,
--by interpolation theory
     rr:=rList(L);
     s:=dim C;
     sum(#L, i-> (-1)^i*rr_i*partialEuler(-L_i,s,C)))

LL(List,ZZ,HashTable) := (L,j,C) ->(
--this function LL(dd,j,C) corresponds to $L(dd, \sigma^j, C)$
--in our paper
     rr:=rList(L);
     s:=#L-2;
     sig:=sigma(s,j);
     sum(#L, i-> (-1)^i*rr_i*partialEuler(-L_i,sig_i,C))
     )

--     apply(#L, i->(-1)^i*rr_i*partialEuler(-L_i,sig_i,C)))


LL(List,HashTable) := (L,C) -> LL(L,#L,C)
--and this one is LL(dd,\sigma, C)



showLL = method()
showLL(List,ZZ) := (L,j) ->(
--this gives the table whose dot product with C is
--LL(L,j,c)
     D:= new MutableHashTable;
     rr:=rList(L);
     s:=#L-2;
     sig:=sigma(s,j);
     apply(#L, i-> (
	       for k from 0 to sig_i do 
		    D#(k,-L_i) = (-1)^(i+k)*rr_i
	       )
	  );
     new CohomologyTally from D
     )

shift=(L,d)->apply(L,i->i+d)
--adds d to each element of the list L

///
--various tests of the code above
restart
load "BS-extensions.m2"
sigma(5,3)
sigma(5)
rList({0,2,4})
D=showLL({0,1,2},3)
D=showLL({0,1,2},2)
D=showLL({0,1,2},1)
peek D


kk = ZZ/32003
S = kk[x_0..x_3]
I1=ideal(x_0,x_1,x_3)  
I2=ideal(x_0,x_1*x_2,x_3)
IC=monomialCurveIdeal(S,{1,2,3})  
IC1=monomialCurveIdeal(S,{1,4,5}) 
I=intersect(IC1,I1)
F=sheaf module I

C=cohomologyTable(F, -10, 2)
partialEuler(-1,4,C)
L={-2,0,2,4,5}
for d from -5 to 5 do print LLTest(shift(L,-3), C)
L={-2,0,2}
showLL(shift(L,-3),4)
for d from -5 to 5 do print LL(shift(L,-d),4,C)

showLL({0,1,4},3)
showLL({0,1,4},2)
C
LL({0,1,4},3, C)
LL({0,1,4},2, C)

L={-2,0,2,4}
C
showLL(shift(L,-5), 4)
LL(shift(L,-5),4,C)
///          

end 

restart
load "BS-extensions.m2"

kk = ZZ/32003
S = kk[x_0..x_3]

I1=ideal(x_0,x_1,x_3)  
I2=ideal(x_0,x_1*x_2,x_3)
IC=monomialCurveIdeal(S,{1,2,3})  
IC1=monomialCurveIdeal(S,{1,4,5}) 
I=intersect(IC1,I1)
F=sheaf module I

C=cohomologyTable(F, -10, 2)
C1=addToTable(C,2,-5,1)
C1=addToTable(C1,3,-5,1)

C2=addToTable(C,3,-3,7)
C2=addToTable(C,3,-3,-7)
C2=addToTable(C2,3,-3,-7)
C2#?(3,-3)
     D=new MutableHashTable from C
D#?(3,-3)
viewHelp HashTable
zeroSequences C
zeroSequences C1

C=cohomologyTable(F, -10, 2)
C1=addToTable(C,2,-8,1)
C1=addToTable(C1,3,-8,1)
zeroSequences C
zeroSequences C1

C=cohomologyTable(F, -10, 2)
C1=addToTable(C,2,-8,-1)
C1=addToTable(C1,3,-8,-1)
zeroSequences C
zeroSequences C1

C2=nextZeroSequence C1
C2 = nextZeroSequence C2

--------------
restart
load "BS-extensions.m2"
kk = ZZ/32003
S = kk[x_0..x_3]

Ipoint=ideal(x_0,x_1,x_3)  
Iline = ideal(x_2,x_3)
IPointAndLine=intersect(Ipoint, Iline)

line = S^1/ideal(x_2,x_3)

plane = S^1/ideal(x_3) - doesn't matter which plane!
--F=sheaf(module Ipoint++line)
F=sheaf(module IPointAndLine++(plane**S^{-2}))
F=sheaf(module Ipoint++(plane**S^{-3}))
C=cohomologyTable(F, -40, 2)
normalizedMultipliers C
C=cohomologyTable(F, -10, 2)
C1=C
C1=nextZeroSequence C1
for m from 1 to 7 do print (C1=nextZeroSequence C1)
zeroSequences C
 zeroSequences C1


C1=addToTable(C,2,-8,1)
C1=addToTable(C1,3,-8,1)
zeroSequences C
zeroSequences C1


---------
restart
--example for the paper, showing that the torsion
--and torsion-free parts of a sheaf get mixed together
--in the decomposition of the coho table.
load "BS-extensions.m2"
kk = ZZ/32003
S = kk[x_0..x_2]
Ipoint=ideal(x_0,x_1)
line = S^1/ideal(x_2)
F=sheaf(module Ipoint++(line**S^{-4}))
C= cohomologyTable(F, -3, 2)
C=3*5*cohomologyTable(F, -6, 2)
C=2^2*3^3*5*7*11^2*13*17*19*151*23*31*41*61*101*cohomologyTable(F, -150, 2)
zeroSequences C
factor 2869
C1=C
for m from 1 to 3 do print (C1=nextZeroSequence C1)

C=cohomologyTable(sheaf module Ipoint, -60, 2)
zeroSequences C
C1=C
for m from 1 to 7 do print (C1=nextZeroSequence C1)
normalizedMultipliers C

-- From Schreyer, Jan 1 2009
restart
load "BS-extensions.m2"
kk = ZZ/32003
S = kk[x_0..x_2]
F=sheaf module ideal (x_0,x_1)
E=sheaf ((coker matrix {{x_2}})**S^{-3})
     C=cohomologyTable(F++E,-80,2)
     --zeroSequences C
     C1=nextZeroSequence C
     for i from 1 to 77 do (C1=nextZeroSequence C1;
	      print (factor (d1=max (values applyValues(C1,c->denominator (c/1)))),d1))
	 applyValues(d1*C1,c->if denominator (c/1)==1 then numerator (c/1) else c)
	 	 applyValues(d1*C1,c->c)
	 applyValues(C1,c->c+0.0)
	 m=C1_(0,1)
	 C1
	 --applyValues(C1,c->c/m+0.0)
	 


--Example of non-cancellation?
restart
load "BS-extensions.m2"
--ideal sheaf of tw cubic and other points on it's Hilb sch
S=kk[a..d]
m=matrix"a,b,c;
b,c,d"
i= minors(2,m)
j=intersect(ideal"a3+b3+c3,d", ideal(a,b,d)) -- cubic with point on the plane
j1=intersect(ideal(a^3), (ideal(a,b))^4)+ideal(d)--triple line with planar emb pt
k=intersect(ideal"a3+b3+c3,d", ideal(a,b,c)) -- cubic with point off the plane
k1=intersect(ideal"a3,d", (ideal(a,b,d))^2) -- triple line with spatial emb pt
hilbertPolynomial(S^1/i)
hilbertPolynomial(S^1/j)
hilbertPolynomial(S^1/j1)
hilbertPolynomial(S^1/k)
hilbertPolynomial(S^1/k1)

MT=N->(
C=cohomologyTable(sheaf module i,-N,5);
D=cohomologyTable(sheaf module j,-N,5);
E=cohomologyTable(sheaf module k,-N,5);
)
--D1=cohomologyTable(sheaf module j1,-10,5)
--E1=cohomologyTable(sheaf module k1,-10,5)
MT(4)
C
E
D
--A table between D and E:
MT(35)
D
D1=addToTable(D,0,2,-1)
D1=addToTable(D1,1,2,-1)
zeroSequences D1
--Passes the test

--A second table between D and E:
MT(4)
D
D1=addToTable(D,0,1,-1)
D1=addToTable(D1,1,1,-1)
zeroSequences D1
--FAILS this test. NOT A COHO TABLE


--A table derived from D by cancellation with the top row.
MT(4)
C
E
D
D1=addToTable(D,2,-4,-1)
D1=addToTable(D1,3,-4,-1)
zeroSequences D1
--FAILS the test


--A table between C and E:
MT(35)
C
E
D
D1=addToTable(E,1,0,-1)
D1=addToTable(D1,2,0,-1)
zeroSequences D1
--Passes this test, though these don't exist!


restart
load "BS-extensions.m2"
kk=ZZ/101
--ideal sheaf of tw cubic and other points on it's Hilb sch
S=kk[a..d]
m=matrix{{a,b,c},{b,c,d}}
i= minors(2,m)
j=intersect(ideal"a3+b3+c3,d", ideal(a,b,d)) -- cubic with point on the plane
j1=intersect(ideal(a^3), (ideal(a,b))^4)+ideal(d)--triple line with planar emb pt
k=intersect(ideal"a3+b3+c3,d", ideal(a,b,c)) -- cubic with point off the plane
k1=intersect(ideal"a3,d", (ideal(a,b,d))^2) -- triple line with spatial emb pt
hilbertPolynomial(S^1/i)
hilbertPolynomial(S^1/j)
hilbertPolynomial(S^1/j1)
hilbertPolynomial(S^1/k)
hilbertPolynomial(S^1/k1)

MT=N->(
     C=cohomologyTable(sheaf module i,-N,5);
     
     D=cohomologyTable(sheaf module j,-N,5);
     
     E=cohomologyTable(sheaf module k,-N,5);
     
     )
D1=cohomologyTable(sheaf module j1,-10,5)
E1=cohomologyTable(sheaf module k1,-10,5)
MT(4)
C
E
D
--between C and E
C=cohomologyTable(sheaf module i,-40,5)
C1=addToTable(C,1,0,1);
C1=addToTable(C1,2,0,1)     -- fails after { -7,1,2}
C1=addToTable(C1,1,-1,1);
C1=addToTable(C1,2,-1,1)  -- fails after {-13,0,1}
C1=addToTable(C1,1,-2,1);
C1=addToTable(C1,2,-2,1)  -- fails after {-26,-1,1}
C1=addToTable(C1,1,-3,1);
C1=addToTable(C1,2,-3,1)  -- fails after {-40,-1,1}

zeroSequences C1


-------------------------------
--ideal sheaf of two skew lines and other points on its Hilbert scheme
restart
load "BS-extensions.m2"
kk=ZZ/101
S=kk[a..d]
i= intersect(ideal(a,b),ideal(c,d)) --two skew lines
j=intersect(ideal"a2+b2+c2,d", ideal(a,b,d)) -- conic with point on plane 
j1=intersect(ideal(a^2), (ideal(a,b))^3)+ideal(d)--double line with planar emb pt
k=intersect(ideal"a2+b2+c2,d", ideal(a,b,c)) -- conic with point off the plane
k1=intersect(ideal"a2,d", ideal(a,b,d^2)) -- double line with spatial emb pt
hilbertPolynomial(S^1/i)
hilbertPolynomial(S^1/j)
hilbertPolynomial(S^1/j1)
hilbertPolynomial(S^1/k)
hilbertPolynomial(S^1/k1)
MT=N->(
     C=cohomologyTable(sheaf module i,-N,5);
     
     D=cohomologyTable(sheaf module j,-N,5);
     
     E=cohomologyTable(sheaf module k,-N,5);
     
     )
D1=cohomologyTable(sheaf module j1,-10,5)
E1=cohomologyTable(sheaf module k1,-10,5)
MT(10)
C
D
E
D1
E1


C=cohomologyTable(sheaf module i,-10,5)
--all tables between C and E seem to fail
C1=addToTable(C,1,-1,1);
C1=addToTable(C1,2,-1,1)  -- fails after { -9,0,1}
C2=C1
C1=addToTable(C1,1,-2,1);
C1=addToTable(C1,2,-2,1) -- fails after {-17,-1,1}
C3=C1
C1=addToTable(C1,1,-3,1);
C1=addToTable(C1,2,-3,1) -- fails after {-27,-1,1}
C4=C1
C1=addToTable(C1,1,-4,1);
C1=addToTable(C1,2,-4,1) -- fails after {-40,-2,1}
C5=C1
C1=addToTable(C1,1,-5,1);
C1=addToTable(C1,2,-5,1) -- fails after ???
C6=C1
zeroSequences(C1)
MT(6)
zeroSequences(E)

C3
showLL(shift({-1,1,2,3},0),2)
LL(shift({-1,1,2,3},0),2,C3)

C2

--Here's the functional negative on C2:
C2
showLL({-1,0,1,2,5},2)
LL({-1,0,1,2,5},2,C2)


--the example above, the functional negative on C2,
-- was found using this loop:
test=(start,Bo,A)->(
     --Bo is a list of 5 bounds
     M:={};
     for  t from 1 to 5 do
     for i0 from start to Bo_0 do
     for i1 from i0+1 to Bo_1 do
     for i2 from i1+1 to Bo_2 do
     for i3 from i2+1 to Bo_3 do
     for i4 from i3+1 to Bo_4 do(
     	  L={i0,i1,i2,i3,i4};
     	  val = LL(L,t,C2);
	  M=M|{val};
	  if val<0 then (
	       print (L,t); 
	       print val);
    	  M)
     )
N=test(-1,{-1,2,3,4,5},C2)






