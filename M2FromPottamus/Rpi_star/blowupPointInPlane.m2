restart
load "betti-fix.m2"
load "local.m2"
load "computingRpi_star.m2"
kk=ZZ/101
A1=kk[a,b,c,Degrees=>{3:{2,0}}]

--I=(ideal{vars A1})^2 -- use for restriction to fat neighbarhood
--I=ideal(a*b)
I=ideal(0_A1)
A=A1/I
setMaxIdeal(ideal(a,b,c))
S1=kk[a,b,x_0,x_1,Degrees=>{2:{2,0},2:{1,1}}]

xx1=matrix{{x_0,x_1}}

S=S1/substitute(I,S1)
setMaxIdeal(ideal(a,b,x_0,x_1))
xx=substitute(xx1,S)
I2=minors(2,matrix{{a,x_0},{b,x_1}})

I3= saturate(I2,ideal(a,b))
I3=I2
transpose gens I3
M1=coker substitute(gens I3,S)
d=3
M=presentation localPrune (((ideal xx)^d)*M1)**S^{{0,d}}
E1=kk[a,b,e_0,e_1,Degrees=>{2:{2,0},2:{1,1}},SkewCommutative=>{2,3}]
E=E1/substitute(I,E1)
setMaxIdeal(ideal(a,b,e_0,e_1))
ee=matrix{{e_0,e_1}}

N=presentation localPrune coker symmetricToExteriorOverA(M,ee,xx)
fN=res(coker N,LengthLimit=>6)
bettiT dual fN
Rs=apply(1..7,i->degreeZeroPart(fN**E^{{0,i}},A)[i-1])
apply(Rs,R->(R.dd_0,R.dd_1))
bettiT dual  fN
fN.dd_1
fN.dd_2
fN.dd_3
fN.dd_4
fN.dd_5






