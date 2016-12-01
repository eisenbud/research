kk:=GF(101);
P5:=ProjectiveSpace(kk, 5);
P<a,b,c,d,e,f> := CoordinateRing(P5);

//L :=[a^3+b^3+a^2*b+a*b^2,c^3+d^3+c^2*d+c*d^2,e^3+f^3+e^2*f];
L1 := &+[Random(kk)*P.i*P.j*P.k : i in [1,2,3,5], j in [1,2,3,5], k in [1,2,6]];
L2 := &+[Random(kk)*P.i*P.j*P.k : i in [1,3,4,5], j in [1,3,4,5], k in [3,4,5]];
L3 := &+[Random(kk)*P.i*P.j*P.k : i in [2,4,5,6], j in [2,4,6], k in [2,4,5,6]];
L := [L1,L2,L3];
X := Scheme(P5, L);
assert(IsSingular(X) eq false);
I = Ideal(L);

/*
J:=JacobianMatrix(L);
M:=Minors(J,3);
Y := Scheme(P5, M cat L);
Degree(Y);
*/


LPlist := [
         P.1,
         P.2,
         P.3,
         P.4
	 ];
LP := Ideal(LPlist);
Dimension(Scheme(P5, LPlist cat L));


load "Rees.m";

R:=P/Ideal([P!x : x in Basis(I)]);
nzd := Basis(LP)[1];
ri, f := rees_ideal(R, LP, nzd);

PZ := Codomain(f);
M := GradedModule(ri);
res := MinimalFreeResolution(M);
res;

load "set_degrees";

BT,topLeft := BettiRes(res,[0],[0: i in [1..6]] cat [1 : i in [1..4]]);
regBettiRes(BT, topLeft);
