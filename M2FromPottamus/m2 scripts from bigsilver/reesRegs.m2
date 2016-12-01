isEquiGenerated = method()
isEquiGenerated (Ideal) := (I) -> (
     L :=flatten  degrees I;
     if max(L)==min(L) then true else false)
     
reesAlgebra = method()
reesAlgebra (Ideal,RingElement) := (I,a) -> (
     R := ring I;
     n := numgens R;
     j := syz gens I;
     m := numgens I;
     newdegs := apply(degrees R, i-> flatten{i,0}) | apply(numgens I, i->flatten {degree(I_i),1});
     S := tensor(R,(coefficientRing R)[Y_0..Y_(m-1)], Degrees=>newdegs, MonomialOrder => GRevLex);
     symm := ideal((substitute(matrix{{S_n..S_(n+m-1)}},S))*substitute(j,S));
     saturate(symm, substitute(a, S)))

reesAlgebra Ideal := (I) -> (
     reesAlgebra (I, I_0))



reesAlgebra0 = method()
reesAlgebra0 Ideal := (I) -> (
     R := ring I;
     n := numgens R;
     j := syz gens I;
     m := numgens I;
     S := tensor(R,(coefficientRing R)[Y_0..Y_(m-1), Degrees=>apply(numgens I, i->degree(I_i))], MonomialOrder => GRevLex);
     symm := ideal((substitute(matrix{{S_n..S_(n+m-1)}},S))*substitute(j,S));
     saturate(symm, substitute(I_0, S)))

weightedBetti = method()
weightedBetti (BettiTally,List) := (B,W) -> (
     dot := (X,Y) -> sum apply(#X, j-> X#j*Y#j);
     new BettiTally from apply(pairs B, i-> (
	       (key,bettivalue) := i;
	       (key#0, prepend(dot(W,key#1),key#1)),
	       bettivalue)))


regularity BettiTally := (B) -> (
     max apply(pairs B, i-> first last i#0 - first i#0))


maxTwist = method()
maxTwist BettiTally := (B) -> (
     max apply(pairs B, i-> first last i#0 ))

stabilizationBound= I->(
     L := reesAlgebra(I);
     maxTwist weightedBetti(betti res L, {0,1}))
     

yReesRegularity = method()
yReesRegularity Ideal := (I) -> (
     L := reesAlgebra(I);
     regularity weightedBetti(betti res L, {0,1}))

xReesRegularity = method()
xReesRegularity Ideal := (I) -> (
     L := reesAlgebra(I);
     regularity weightedBetti(betti res L, {1,0}))


yRR = yReesRegularity  
xRR = xReesRegularity     

deg1Coef = (I) -> (
     bBound := stabilizationBound I;
     regList := apply(bBound, i-> regularity(I^i));
     regList#(bBound-1) -regList#(bBound-2))

deg0Coef = (I) -> (
     bBound := stabilizationBound I;
     a := deg1Coef(I);
     last apply(bBound, i-> regularity(I^i)-a*i))     

end  
  
  
restart
load "reesRegs.m2"

R=ZZ/101[a..e]
I=monomialCurveIdeal(R, {1,2,3,5})
RI=reesAlgebra(I)
S=ring RI
C=res RI
betti C

bBound = xRR I -- 
m=stabilizationBound I
regList = apply(1..m, i-> regularity(I^i))
a = regList#(m-1) -regList#(m-2)
b = apply(1..m-1, i-> regularity(I^i)-a*i)


I=monomialCurveIdeal(R, {1,2,3,6})
RI=reesAlgebra(I)
bBound = xRR I -- 
m=stabilizationBound I
regList = apply(1..m, i-> regularity(I^i))
a = regList#(m-1) -regList#(m-2)
b = apply(1..m-1, i-> regularity(I^i)-a*i)

--------------------------------

restart	  
load "reesRegs.m2"
kk=ZZ/101
--S=kk[x,y]
--

S=kk[x,y]
I=ideal"x6,y11,x5y10"
RI=reesAlgebra(I)
bBound = xRR I -- 
m=stabilizationBound I
regList = apply(1..10, i-> regularity(I^i))
a = regList#(m) -regList#(m-1)
b = apply(1..m-1, i-> regularity(I^i)-a*i)


R=ZZ/101[x,y,u,v]
d=3
test = d -> ( 
I := ideal(x^d, y^d, u^(d-1)*x-v^(d-1)*y);
-- regularity(I)
RI := reesAlgebra(I);
S := ring RI;
weightedBetti(betti res RI,{0,1});
print (stabilize := maxTwist weightedBetti(betti res RI, {0,1}));
print (bBound := xRR I - 1) ; 
regList := apply(stabilize, i-> regularity(I^i));
print (apply(length(regList)-1, i -> regList#(i+1)-regList#i)); 
print "a="; print (a := regList#(stabilize-1) -regList#(stabilize-2));
print (remList = apply(stabilize, i-> regularity(I^i)-a*i));
print (b := last remList);
)
test 3


