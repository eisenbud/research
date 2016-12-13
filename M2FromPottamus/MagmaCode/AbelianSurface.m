//The ideal of a smooth abelian surface of degree 10 in P4,
//as computed by M2, in Magma syntax.
k := GF(23003);
P<x_0,x_1,x_2,x_3,x_4> := PolynomialRing(k,5,"grevlex");
I := ideal< P | 
         x_0^2*x_1^2*x_3-x_0^3*x_2*x_3+x_0*x_2^2*x_3^2-x_0*x_1*x_3^3+x_1^2*x_2^2*x_4-x_0*x_2^3*x_4-x_1^3*x_3*x_4-x_0*x_1*x_2*x_3*x_4+x_0^2*x_2*x_4^2+x_1*x_3^2*x_4^2-x_1*x_2*x_4^3,
         x_0*x_1^3*x_2-x_0^2*x_1*x_2^2+x_1*x_2^3*x_3-x_1^2*x_2*x_3^2+x_0^3*x_1*x_4+x_0*x_1*x_2*x_3*x_4-x_0^2*x_3^2*x_4+x_2*x_3^3*x_4-x_0*x_1^2*x_4^2-x_2^2*x_3*x_4^2+x_0*x_3*x_4^3,
         x_0^5+x_1^5+x_0^2*x_1*x_2^2+x_2^5+x_0^3*x_2*x_3+x_1^2*x_2*x_3^2+x_0*x_1*x_3^3+x_3^5+x_0*x_2^3*x_4+x_1^3*x_3*x_4-5*x_0*x_1*x_2*x_3*x_4+x_0^2*x_3^2*x_4+x_0*x_1^2*x_4^2+x_2^2*x_3*x_4^2+x_1*x_2*x_4^3+x_4^5,
         x_0*x_1^2*x_3^3-x_0^2*x_2*x_3^3+x_2^2*x_3^4-x_1*x_3^5-x_1^4*x_3*x_4+x_0*x_1^2*x_2*x_3*x_4-x_2^3*x_3^2*x_4-x_1*x_2*x_3^3*x_4-x_0^3*x_3*x_4^2-x_1^2*x_3^2*x_4^2+2*x_0*x_2*x_3^2*x_4^2+x_1^2*x_2*x_4^3-x_0*x_2^2*x_4^3-x_0*x_1*x_3*x_4^3+x_0^2*x_4^4-x_1*x_4^5,
         x_0*x_1^2*x_2*x_3^2-x_0^2*x_2^2*x_3^2+x_2^3*x_3^3-x_1*x_2*x_3^4-x_1^4*x_2*x_4+x_0*x_1^2*x_2^2*x_4-x_2^4*x_3*x_4-x_1*x_2^2*x_3^2*x_4-x_0^2*x_1^2*x_4^2-x_1^2*x_2*x_3*x_4^2+x_0*x_2^2*x_3*x_4^2+x_0*x_1*x_3^2*x_4^2+x_1^3*x_4^3-x_1*x_3*x_4^4,
         x_0*x_1^4*x_3-x_0^3*x_2^2*x_3+x_1^2*x_2^2*x_3^2+x_0*x_2^3*x_3^2-x_1^3*x_3^3-x_0*x_1*x_2*x_3^3+x_1^2*x_2^3*x_4-x_0*x_2^4*x_4+x_0^4*x_3*x_4-x_1^3*x_2*x_3*x_4-x_0*x_1*x_2^2*x_3*x_4+x_0*x_1^2*x_3^2*x_4-x_0^2*x_2*x_3^2*x_4+x_1*x_3^4*x_4-x_0*x_1^2*x_2*x_4^2+2*x_0^2*x_2^2*x_4^2+x_0^2*x_1*x_3*x_4^2-x_0^3*x_4^3-x_1*x_2^2*x_4^3+x_0*x_1*x_4^4,
         x_1^2*x_2^4-x_0*x_2^5-x_0^4*x_2*x_3-x_1^3*x_2^2*x_3-x_0*x_1*x_2^3*x_3-x_0^2*x_2^2*x_3^2+x_0^2*x_1*x_3^3-x_0*x_3^5+x_0^2*x_2^3*x_4+x_0^2*x_1*x_2*x_3*x_4+2*x_1*x_2^2*x_3^2*x_4-x_1^2*x_3^3*x_4-x_0*x_2*x_3^3*x_4-x_1*x_2^3*x_4^2+x_3^4*x_4^2-x_2*x_3^2*x_4^3,
         x_1^3*x_2^3-x_0*x_1*x_2^4-x_0^4*x_1*x_3-x_1^4*x_2*x_3-x_0*x_1^2*x_2^2*x_3-x_0^2*x_1*x_2*x_3^2+x_0^3*x_3^3-x_0*x_2*x_3^4+x_0^2*x_1*x_2^2*x_4+x_0^3*x_2*x_3*x_4+x_1^2*x_2*x_3^2*x_4+x_0*x_1*x_3^3*x_4-2*x_1^2*x_2^2*x_4^2+x_0*x_2^3*x_4^2+x_1^3*x_3*x_4^2+x_0*x_1*x_2*x_3*x_4^2-x_0^2*x_3^2*x_4^2-x_0^2*x_2*x_4^3-x_1*x_3^2*x_4^3+x_1*x_2*x_4^4,
         x_0*x_1^2*x_2^3-x_0^2*x_2^4+x_2^5*x_3-x_1*x_2^3*x_3^2+x_0^3*x_2^2*x_4+x_0*x_2^3*x_3*x_4-x_0*x_1*x_2*x_3^2*x_4+x_2*x_3^4*x_4+x_1^3*x_2*x_4^2-2*x_0*x_1*x_2^2*x_4^2+x_2^2*x_3^2*x_4^2+x_0^2*x_1*x_4^3+x_1*x_2*x_3*x_4^3-x_0*x_3^2*x_4^3-x_1^2*x_4^4+x_3*x_4^5,
         x_1^4*x_2^2-x_0^2*x_2^4+2*x_2^5*x_3+x_0^3*x_2*x_3^2+x_0*x_2^2*x_3^3-x_0*x_1*x_3^4+x_3^6+2*x_0^2*x_1^2*x_2*x_4+x_1^2*x_2^2*x_3*x_4+x_0*x_2^3*x_3*x_4+x_1^3*x_3^2*x_4-5*x_0*x_1*x_2*x_3^2*x_4+2*x_2*x_3^4*x_4+x_0^4*x_4^2-2*x_0*x_1*x_2^2*x_4^2+x_0^2*x_2*x_3*x_4^2+x_2^2*x_3^2*x_4^2+x_1*x_3^3*x_4^2+x_1*x_2*x_3*x_4^3-x_1^2*x_4^4+2*x_3*x_4^5,
         x_0^2*x_1^2*x_2^2-x_0^3*x_2^3+x_0*x_2^4*x_3-x_0*x_1*x_2^2*x_3^2+x_0^4*x_2*x_4+x_0^2*x_2^2*x_3*x_4-x_0^2*x_1*x_3^2*x_4+x_0*x_3^4*x_4-x_0^2*x_1*x_2*x_4^2-x_1*x_2^2*x_3*x_4^2+x_1^2*x_3^2*x_4^2+x_0*x_2*x_3^2*x_4^2-x_3^3*x_4^3+x_2*x_3*x_4^4,
         x_1^5*x_2-x_0^2*x_1*x_2^3+2*x_1*x_2^4*x_3+x_0^3*x_1*x_3^2+x_0*x_1*x_2*x_3^3-x_0^2*x_3^4+x_2*x_3^5+x_0^2*x_1^3*x_4+x_0^3*x_1*x_2*x_4+x_1^3*x_2*x_3*x_4-2*x_0*x_1^2*x_3^2*x_4-x_0^2*x_2*x_3^2*x_4-x_1^4*x_4^2-x_0*x_1^2*x_2*x_4^2-x_2^3*x_3*x_4^2+x_0*x_3^3*x_4^2+x_1^2*x_3*x_4^3+x_0*x_2*x_3*x_4^3,
         x_0^3*x_1^2*x_2-x_0^4*x_2^2+x_0^2*x_2^3*x_3+x_0*x_1^3*x_3^2-2*x_0^2*x_1*x_2*x_3^2+x_1*x_2^2*x_3^3-x_1^2*x_3^4-x_1^5*x_4-x_0^2*x_1*x_2^2*x_4-x_2^5*x_4-x_1^2*x_2*x_3^2*x_4-x_0^3*x_1*x_4^2-x_0*x_2^3*x_4^2-x_1^3*x_3*x_4^2+4*x_0*x_1*x_2*x_3*x_4^2-x_2*x_3^3*x_4^2-x_0*x_1^2*x_4^3-x_2^2*x_3*x_4^3-x_1*x_2*x_4^4+x_0*x_3*x_4^4-x_4^6,
         x_1^6-x_0^3*x_2^3+2*x_1^2*x_2^3*x_3+x_0*x_2^4*x_3+x_0^4*x_3^2-x_0*x_1*x_2^2*x_3^2-x_2^2*x_3^4+2*x_1*x_3^5+2*x_0^3*x_1^2*x_4+x_0^4*x_2*x_4+2*x_1^4*x_3*x_4-4*x_0*x_1^2*x_2*x_3*x_4+3*x_0^2*x_2^2*x_3*x_4-x_0^2*x_1*x_3^2*x_4+2*x_1*x_2*x_3^3*x_4+x_0*x_3^4*x_4-x_0^2*x_1*x_2*x_4^2+x_2^4*x_4^2-x_1*x_2^2*x_3*x_4^2+2*x_1^2*x_3^2*x_4^2-x_0*x_2*x_3^2*x_4^2+2*x_0*x_1*x_3*x_4^3-x_3^3*x_4^3-x_0^2*x_4^4+x_2*x_3*x_4^4+2*x_1*x_4^5,
         x_0*x_1^5-x_0^3*x_1*x_2^2+x_1^3*x_2^2*x_3+x_0*x_1*x_2^3*x_3-x_1^4*x_3^2-x_0^2*x_2^2*x_3^2+x_2^3*x_3^3-x_1*x_2*x_3^4+2*x_0^4*x_1*x_4-x_1^4*x_2*x_4+x_0*x_1^2*x_2^2*x_4+x_0*x_1^3*x_3*x_4-x_2^4*x_3*x_4-x_0^3*x_3^2*x_4-x_1*x_2^2*x_3^2*x_4+x_1^2*x_3^3*x_4+x_0*x_2*x_3^3*x_4-x_0^2*x_1^2*x_4^2+x_1*x_2^3*x_4^2-3*x_1^2*x_2*x_3*x_4^2+x_0*x_1*x_3^2*x_4^2+x_1^3*x_4^3+x_0*x_1*x_2*x_4^3+x_2*x_3^2*x_4^3-x_2^2*x_4^4-x_1*x_3*x_4^4+x_0*x_4^5,
         x_0^2*x_1^4-x_0^4*x_2^2+2*x_0*x_1^2*x_2^2*x_3-2*x_0^2*x_1*x_2*x_3^2+x_2^4*x_3^2-x_1^2*x_3^4-2*x_1^5*x_4-2*x_0^2*x_1*x_2^2*x_4-2*x_2^5*x_4-2*x_1^2*x_2*x_3^2*x_4-x_1^2*x_2^2*x_4^2+6*x_0*x_1*x_2*x_3*x_4^2-x_0^2*x_3^2*x_4^2-2*x_0*x_1^2*x_4^3-2*x_2^2*x_3*x_4^3-2*x_1*x_2*x_4^4+2*x_0*x_3*x_4^4-x_4^6,
         x_0^3*x_1^3-x_0^4*x_1*x_2+x_0^2*x_1*x_2^2*x_3-x_0^3*x_2*x_3^2+x_0*x_2^2*x_3^3-x_0*x_1*x_3^4-x_0*x_1^4*x_4-x_0^2*x_1^2*x_2*x_4-x_1*x_2^4*x_4+2*x_1^2*x_2^2*x_3*x_4-x_0*x_2^3*x_3*x_4-x_1^3*x_3^2*x_4-x_0*x_1*x_2*x_3^2*x_4-x_0*x_1*x_2^2*x_4^2+x_0*x_1^2*x_3*x_4^2+2*x_0^2*x_2*x_3*x_4^2-x_2^2*x_3^2*x_4^2+x_1*x_3^3*x_4^2+x_2^3*x_4^3-x_1*x_2*x_3*x_4^3-x_0*x_2*x_4^4,
         x_0^4*x_1^2+2*x_0^2*x_1*x_2^3+x_2^6+2*x_0^3*x_2^2*x_3-2*x_1*x_2^4*x_3-2*x_0^3*x_1*x_3^2+x_1^2*x_2^2*x_3^2+x_0^2*x_3^4-2*x_0^2*x_1^3*x_4-2*x_0^3*x_1*x_2*x_4-4*x_0*x_1*x_2^2*x_3*x_4+2*x_0*x_1^2*x_3^2*x_4+2*x_0^2*x_2*x_3^2*x_4+x_1^4*x_4^2+2*x_0*x_1^2*x_2*x_4^2-x_0^2*x_2^2*x_4^2+2*x_0^2*x_1*x_3*x_4^2+2*x_2^3*x_3*x_4^2-2*x_0*x_3^3*x_4^2+2*x_1*x_2^2*x_4^3-2*x_1^2*x_3*x_4^3-2*x_0*x_2*x_3*x_4^3+x_3^2*x_4^4>;

M := MonomialsOfDegree(P,1);
LP := Ideal([&+[Random(k)*m: m in M]: c in [1 .. 4]]);

//k:=GF(32003);
//n:=5;
/*
load "Rees.m";

R:=P/I;
nzd := Basis(LP)[1];
ri, f := rees_ideal(R, LP, nzd);

PZ := Codomain(f);
M := GradedModule(ri);

time res := MinimalFreeResolution(M);
res;

load "set_degrees";

time BT,topLeft := BettiRes(res,[0],[0,0,0,0,0,1,1,1,1]);
regBettiRes(BT, topLeft); 


 The regularity of the rees ideal is 10 in this case
[  0   0   0   0   2   8  12   8   2]
[  0   0   0  20  83 130  90  20   2]
[  0   0  35 165 303 260  71  15   4]
[  0  18 113 275 343 125  56  28   2]
[  1  23 107 243 120 125  84  22   6]
[  0  17  93  62 170 140  81  30   0]
[  0  15  15 137 140 145  66   8   2]
[  0   1  60  84 140  90  40  10   0]
[  0  11  28  72  90  80  21   0   0]
[  0   4  17  66  80  25   0   0   0]
[  0   1  30  40  20   0   0   0   0]
[  0   6   8  12   0   0   0   0   0]
[  0   0   5   0   0   0   0   0   0]
[  0   1   0   0   0   0   0   0   0]


for i:=1 to 10 do
print relative_regularity(LP, I, i);
end for;
*/