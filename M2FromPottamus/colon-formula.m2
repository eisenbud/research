--Testing the Boij-Soderberg Conjecture.

--The betti diagram of a pure degree sequence:
restart


pureBetti=Degs-> (
     --Degs must be a strictly increasing list of positive integers
     c:= # Degs;
     p:=1;
     for i from 1 to c-1 do (for j from 0 to i-1 do p=p*(Degs_i-Degs_j));
     D:=for i from 0 to c-1 list(
         (-1)^i* product(i, j->Degs_j-Degs_i)*product(i+1..c-1, j->Degs_j-Degs_i));
     Bettis=for i from 0 to c-1 list (p/D_i);
     Bettis=Bettis/(gcd Bettis))

///
L=(0,3,4,5)
pureBetti L 
///

     

Given a betti diagram, use their algorithm to decode it:

S=kk[vars(0..7)]
M=genericMatrix(S, 2, 4)
I=minors (2,M)
B=betti res I
peek B
BB=new BettiTally
BB

weightedBetti (BettiTally,List) := (B,W) -> (
     dot := (X,Y) -> sum apply(#X, j-> X#j*Y#j);
     new BettiTally from apply(pairs B, i-> (
	       (key,bettivalue) := i;
	       (key#0, prepend(dot(W,key#1),key#1)),
	       bettivalue)))

pureBettiDiagram = (Degs) -> (
     Bettis:=pureBetti L;
     new BettiTally from apply(Degs, i-> (
	       (key,bettivalue) := (Degs_i,Bettis_i))))

end
restart
load "BoijSoderbert.m2"
L=(0,3,4,5)
pureBettiDiagram L 
