load "/home/david/magma-mode/.magma"
SetLineEditor(false);
%P #to print all the commands thus far

//////////

// If and only if you want more info:
SetVerbose("Groebner", 1);
SetVerbose("Resolution", 1);

//////////

function my_power_min(I, e)
    if e eq 1 then
	return I;
    elif IsOdd(e) then
	IB := MinimalBasis(I);
	JB := MinimalBasis(my_power(I, e - 1));
	return Ideal([f*g: f in IB, g in JB]);
    else
	JB := MinimalBasis(my_power(I, e div 2));
	return Ideal([f*g: f, g in JB]);
    end if;
end function;

function my_power(I, e)
    // IB := MinimalBasis(I);
    IB := GroebnerBasis(I);
    J := I;
    for i := 2 to e do
	// JB := MinimalBasis(J);
	JB := GroebnerBasis(J);
	J := Ideal([f*g: f in IB, g in JB]);
    end for;
    return J;
end function;

function relative_regularity(LP, I, d)
    LPd := my_power(LP, d);
    ILPd := I+LPd;
    assert IsZeroDimensional(ILPd);
    return Max([Degree(f): f in GroebnerBasis(ILPd)]) - d;
end function;

function rees_ideal(R, LP, nzd)

    n := Rank(R);
    I := DivisorIdeal(R);
    P := Generic(I);
    k := BaseRing(P);

    M:=sub<EModule(R, 1) | [[f]: f in Basis(LP)]>;
    SB := MinimalBasis(MinimalSyzygyModule(M));

    r := #Basis(LP);
    PZ := PolynomialRing(k, n + r, "grevlex");
    AssignNames(
	~PZ, [Sprint(P.i): i in [1..n]] cat [Sprintf("z%o", i): i in [1..r]]
    );
    f := hom<P -> PZ | [PZ.i: i in [1 .. n]]>;
    IZ := Ideal(f(Basis(I)));
    RZ := PZ/IZ;
    phiz := Matrix([[f(v[j]): j in [1..Ncols(v)]]: v in SB]);
    zmat := Matrix([[PZ.(n + j)]: j in [1..r]]);
    mat := phiz*zmat;
    J := IZ + Ideal(Eltseq(mat));
    S := PZ/J;
    g := f(nzd);
    return Saturation(J, g), f;

end function;

//////////

k:=GF(32003);
n:=5;
P<[x]>:=PolynomialRing(k,n,"grevlex");
pows := func<P, e | Ideal(MonomialsOfDegree(P, e))>;
f1 := &+[Random(k)*m: m in Basis(pows(P,3))];
f2 := &+[Random(k)*m: m in Basis(pows(P,3))];
I := Ideal([f1,f2]);
R:=P/I;
LP := ideal <P | [&+[Random(k)*m : m in Basis(pows(P,1))] : i in [1..4]]>;
Groebner(LP);
LP;
//LP := ideal <P | [P.i: i in [1 .. Rank(P)]]>;   // variables
L := ideal<R | Basis(LP)>;

r := #Basis(LP);
nzd := Basis(LP)[1];
ri, f := rees_ideal(R, LP, nzd);
PZ := Codomain(f);
M := GradedModule(ri);
res := FreeResolution(M);
res;
BettiTable(res);
Regularity(M);
sp := hom<PZ -> PZ | [PZ.i: i in [1..n]] cat [1: i in [1..r]]>;
B := BoundaryMaps(res);


NCI := ri + Ideal(f(Basis(LP)));



J:=&*[L : i in [1..3]];
K:=ideal<R | [R!g : g in Basis(pows(P,5))]>;
J subset K;

time LP2:=LP^2;
Groebner(LP2);
time LP4:=LP2^2;
Groebner(LP4);
time LP8:=LP4^2;
Groebner(LP8);

ILP8 := I+LP8;
M := GradedModule(ILP8);
time Regularity(M);
time Regularity(GradedModule(LeadingMonomialIdeal(ILP8)));

time LP9 := LP8*LP;
time Groebner(LP9);
time Regularity(GradedModule(LeadingMonomialIdeal(I + LP9)));

time LP10 := LP9*LP;
time Groebner(LP10);
time Regularity(GradedModule(LeadingMonomialIdeal(I + LP10)));

time LP11 := LP10*LP;
time Groebner(LP11);
time Regularity(GradedModule(LeadingMonomialIdeal(I + LP11)));

time LP12 := LP11*LP;
time Groebner(LP12);
time Regularity(GradedModule(LeadingMonomialIdeal(I + LP12)));

time LP13 := LP12*LP;
time Groebner(LP13);
time Regularity(GradedModule(LeadingMonomialIdeal(I + LP13)));



function asymptotic_regularity(LP, I)
end function;

d := 15;
time LPd := my_power(LP, d);
ILPd := I+LPd;
time Groebner(ILPd);

M := GradedModule(ILPd);
time Groebner(M);
time Regularity(M);


d := 8;
time Regularity(GradedModule(I+(LP^d)));

regs:=[Regularity(GradedModule(I+(LP^d))) : d in [1..4]]; regs;
time for d in [4..7] do
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

//Example from M2
k:=GF(32003);
n:=5;
P<[x]>:=PolynomialRing(k,n,"grevlex");
pows := func<P, e | Ideal(MonomialsOfDegree(P, e))>;

//f1 := sum(0..n, i->x_i^3)+x_0*x_1*x_2
f1:=&+[P.i^3 : i in [1..n]]+ P.1*P.2*P.3 ; f1;

//f2 := sum(0..n, i->(x_i-(i-i+1)*x_((i+1)%(n+1)))^3)) 
f2 := &+[(P.i-P.(i+1))^3: i in [1..4]] + (P.5-P.1)^3;

I := Ideal([f1,f2]);
R:=P/I;
//LP := ideal <P | [&+[Random(k)*m : m in Basis(pows(P,1))] : i in [1..4]]>;
LP := ideal <P | [P.i : i in [2..5]]>; LP;
Groebner(LP);
LP;
//LP := ideal <P | [P.i: i in [1 .. Rank(P)]]>;   // variables
L := ideal<R | Basis(LP)>;

r := #Basis(LP);
nzd := Basis(LP)[1];
ri, f := rees_ideal(R, LP, nzd);



PZ := Codomain(f);
M := GradedModule(ri);
res := MinimalFreeResolution(M);
//	THIS IDEAL HAS A DIFFERENT NUMBER OF GENS THAN THE M2 VERSION!
res;
BettiTable(res);
Regularity(M);

//The following is correct. But there's trouble
//if we use P instead of P/(0).
R:=P/(Ideal(P!0)); R;
P1 := Ideal([R.i : i in [1..n]]);P1;
ri, f := rees_ideal(R,P1, P.1); ri;

//The following produces an error msg
P0 := Ideal(R!1); P0;
ri, f := rees_ideal(R,P0, P.1); ri;

//
R:=P/(Ideal(P.1)); R;
//The following gives an error msg.-- why??
P1 := Ideal([R.i : i in [2..n]]);P1;
ri, f := rees_ideal(R,P1, P.1); ri;
