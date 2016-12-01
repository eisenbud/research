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
     D#(i,d)=D#(i,d)+n;
     new CohomologyTally from D)
     
          
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
	 
