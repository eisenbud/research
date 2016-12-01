restart
-- blow-up of P^2
load "computingRpi_star.m2"
kk=ZZ/101
S=kk[a,b,x_0,x_1,Degrees=>{2:{2,0},2:{1,1}}]
xx=matrix{{x_0,x_1}}
A=kk[a,b,Degrees=>{2:{2,0}}]
E=kk[a,b,e_0,e_1,Degrees=>{2:{2,0},2:{1,1}},SkewCommutative=>true]
ee=matrix{{e_0,e_1}}
use S
M=cokernel matrix{{x_0*a-x_1*b}}
d=3
m=presentation ((ideal(x_0,x_1))^d*M)**S^{{0,d}}
N=symmetricToExteriorOverA(m,ee,xx)
fN=(res(coker N, LengthLimit=>2*d-1))[d-1]**E^{{0,d}}
bettiT dual(fN)
degreeZeroPart(fN,A)
Rpis=apply(-3..3,i->degreeZeroPart(fN[i]**E^{{0,i}},A))
apply(Rpis,c->bettiT dual(c))
bettiT dual(fN)
apply(Rpis,c->(c.dd_1,c.dd_0))


restart
-- blow-up of the ideal (a^3,a^2*b,b^3)
load "computingRpi_star.m2"
kk=ZZ/101
S=kk[a,b,x_0,x_1,x_2,Degrees=>{2:{2,0},3:{1,1}}]
xx=matrix{{x_0,x_1,x_2}}
A=kk[a,b,Degrees=>{2:{2,0}}]
E=kk[a,b,e_0,e_1,e_2,Degrees=>{2:{2,0},3:{1,1}},SkewCommutative=>true]
ee=matrix{{e_0,e_1,e_2}}
use S 
mm=matrix{{x_0,x_1,x_2},{a^3,a^2*b,b^3}}
J=saturate(minors(2,mm),ideal(a,b))
M=S^1/J
d=6
m=presentation ((ideal(x_0,x_1,x_2))^d*M)**S^{{0,d}}
N=symmetricToExteriorOverA(m,ee,xx)
fN=(res(coker N, LengthLimit=>2*d-1))[d-1]**E^{{0,d}}

--tex bettiT dual(fN)
bettiT dual(fN)
--      index: -6 -5 -4 -3 -2 -1 0 1 2  3  4  5
--         -1: 21 18 15 12  9  6 3 1 .  .  .  .
--          0: 20 17 14 11  8  5 3 3 6  9 12 15
--          1:  1  1  1  1  1  1 2 5 8 11 14  .

T=degreeZeroPart(fN,A)
prune HH^(-1)(T)
prune HH^0(T)
bettiT dual chainComplex(fN.dd_1)
fN.dd_3

H1=prune HH^1 T
fH1=res H1
T.dd_1,T.dd_0,T.dd_(-1)

fH1.dd
Rpis=apply(-3..3,i->degreeZeroPart(fN[i]**E^{{0,i}},A))
apply(Rpis,c->bettiT dual(c))
Ts=apply(Rpis,c->chainComplex(c.dd_(-1),c.dd_0,c.dd_1,c.dd_2)[2])
apply(Ts,c->bettiT dual(c))
apply(Ts,c->c.dd)
bettiT dual(Ts#4)
--    index: -1 0 1
--       -1:  . . 3
--        0:  . 5 .
--        1:  1 . .

(Ts#4).dd
--      -2 : 0 <----- A  : -1
--                0
--
--            3                                5
--      -1 : A  <---------------------------- A  : 0
--                 {13, 0} | b -a 0  0  0 |
--                 {13, 0} | 0 0  -a -b 0 |
--                 {13, 0} | 0 0  0  -a b |
--
--           5                      1
--      0 : A  <------------------ A  : 1
--                {15, 0} | -a |
--                {15, 0} | -b |
--                {15, 0} | 0  |
--                {15, 0} | 0  |
--                {15, 0} | 0  |
--
--           1
--      1 : A  <----- 0 : 2
--                0
-- not quasi isomorphic to cohomology



prune HH^0 (Ts#4)
prune HH^1 (Ts#4)
prune HH^(-1) (Ts#4)

--------------------------
restart
load "computingRpi_star.m2"
kk=ZZ/101
S=kk[a,x_0,x_1,x_2,x_3,Degrees=>{1:{2,0},4:{1,1}}]
xx=matrix{{x_0,x_1,x_2,x_3}}
A=kk[a,Degrees=>{1:{2,0}}]
E=kk[a,e_0,e_1,e_2,e_3,Degrees=>{1:{2,0},4:{1,1}},SkewCommutative=>true]
ee=matrix{{e_0,e_1,e_2,e_3}}
use S