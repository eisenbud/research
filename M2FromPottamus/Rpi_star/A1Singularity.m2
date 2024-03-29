restart
load "local.m2"
load "computingRpi_star.m2"
kk=ZZ/101
S1=kk[a,b,c,x_0,x_1,x_2,Degrees=>{3:{2,0},3:{1,1}}]
E1=kk[a,b,c,e_0,e_1,e_2,Degrees=>{3:{2,0},3:{1,1}},SkewCommutative=>{3,4,5}]
A1=kk[a,b,c,Degrees=>{3:{2,0}}]

I=ideal{a^2+b^2+c^2}
A=A1/I
setMaxIdeal(ideal(a,b,c))


xx1=matrix{{x_0,x_1,x_2}}

S=S1/substitute(I,S1)
setMaxIdeal(ideal(a,b,c,x_0,x_1,x_2))
xx=substitute(xx1,S)
I2=minors(2,matrix{{a,x_0},{b,x_1},{c,x_2}})
I3= saturate(I2,ideal(a,b,c))
E=E1/substitute(I,E1)
setMaxIdeal(ideal(a,b,c,e_0,e_1,e_2))
ee=matrix{{e_0,e_1,e_2}}


transpose gens I3
M1=coker substitute(gens I3,S)
d=3
M=presentation localPrune (((ideal xx)^d)*M1)**S^{{0,d}}
N=presentation localPrune coker symmetricToExteriorOverA(M,ee,xx)
fNstrict=res coker N

bettiT dual fNstrict

M1=coker substitute(gens I2,S)
M=presentation localPrune (((ideal xx)^d)*M1)**S^{{0,d}}
N=presentation localPrune coker symmetricToExteriorOverA(M,ee,xx)

fNtotal=res coker N
bettiT dual fNtotal
bettiT dual fNstrict


transpose gens I3
M1=coker substitute(gens I3,S)
d=3
M=presentation localPrune (((ideal xx)^d)*M1)**S^{{0,d}}

E=E1/substitute(I,E1)
setMaxIdeal(ideal(a,b,c,e_0,e_1,e_2))
ee=matrix{{e_0,e_1,e_2}}

N=presentation localPrune coker symmetricToExteriorOverA(M,ee,xx)
res coker N
fN=(localResolution(coker N,LengthLimit=>2*d))[d-1]**E^{{d-1,d}}
bettiT dual fN


use A
localResolution localPrune coker gens((ideal(a,b,c))^4)
R=degreeZeroPart(fN**E^{{0,-3}},A)
bettiT dual R
localPrune HH^1(R)
localPrune HH^2(R)
localPrune HH^3 R
localPrune HH^4 R
setMaxIdeal(ideal vars A1)
m1=lift(R.dd_(-2),A1)
m2=lift(R.dd_(-1),A1)
m3=lift(R.dd_(0),A1)
m1*m2
m0=transpose localsyz transpose m1
m0*m1 -- localsyz changes basis
betti res coker m0
localPrune coker localsyz transpose R.dd_(-2)












