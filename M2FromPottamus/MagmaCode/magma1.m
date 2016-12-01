load "/home/david/magma-mode/.magma"
SetLineEditor(false);
%P #to print all the commands thus far

k:=GF(32003);
n:=5;
P<[x]>:=PolynomialRing(k,n,"grevlex");
pows := func<P, e | Ideal(MonomialsOfDegree(P, e))>;
f1 := &+[Random(k)*m: m in Basis(pows(P,3))];
f2 := &+[Random(k)*m: m in Basis(pows(P,3))];
I := Ideal([f1,f2]);
R:=P/I;
LP := ideal <P | [&+[Random(k)*m : m in Basis(pows(P,1))] : i in [1..4]]>; LP;
L := ideal<R | [&+[Random(k)*(R!m): m in Basis(pows(P,1))] : i in [1..4]]>;
J:=&*[L : i in [1..3]];
K:=ideal<R | [R!g : g in Basis(pows(P,5))]>;
J subset K;
regs:=[Regularity(GradedModule(I+(LP^d))) : d in [1..4]]; regs;

for d in [4..7] do
print(Regularity(GradedModule(I+(LP^d))));
end for;

// this gives regularity(P/(I+LP^d)) = d+2.
//Also
MP := pows(P,1);
for d in [4..7] do
print(MP^(d+3) subset (I+(LP^d))));
end for;
// says "true" for each value. Takes pretty long. d=6 took perhaps 10 min before I killed it
// It didn't want to interrupt!

I5:= pows(P, 5);
I := ideal<P | x>;
k:=GF(32003);

// Dimension(GradedModule(J)); gives an error.
// Dimension(J); seems ok
// HilbertFunction doesn'nt seem to apply to graded modules!

P<x,y,z>:=PolynomialRing(k,3);
P<x,y,z>:=PolynomialRing(k,3,"grevlex");
Grading(P);
P5:=MonomialsOfDegree(P,5);
ideal<P | P5>;
ideal<P | [x]>;
I := ideal< P | x,y>;
I := ideal< P | [x,y]>;
P/(ideal<P | x^2>)

Rank(R);
?Cluster
load "H103E14"

f := &+[Random(k)*m: m in P3];
f;
I3:=Ideal([f1,f2]);
B:=[R!m: m in MonomialsOfDegree(P, 1)];
B;
[g^4: g in B];
