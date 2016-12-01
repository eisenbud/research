restart
load "local.m2"
load "computingRpi_star.m2"
kk=ZZ/101
S1=kk[a,b,x_0,x_1,Degrees=>{2:{2,0},2:{1,1}}]
E1=kk[a,b,e_0,e_1,Degrees=>{2:{2,0},2:{1,1}},SkewCommutative=>true]
A1=kk[a,b,Degrees=>{2:{2,0}}]

I=ideal{a*b}
A=A1/I
setMaxIdeal(ideal(a,b))


xx1=matrix{{x_0,x_1}}

S=S1/substitute(I,S1)
setMaxIdeal(ideal(a,b,x_0,x_1))
xx=substitute(xx1,S)
I2=minors(2,matrix{{a,x_0},{b,x_1}})
I3= saturate(I2,ideal(a,b))
E=E1/substitute(I,E1)
setMaxIdeal(ideal(a,b,e_0,e_1))
ee=matrix{{e_0,e_1}}


transpose gens I3
M1=coker substitute(gens I3,S)
d=3
M=presentation localPrune (((ideal xx)^d)*M1)**S^{{0,d}}
N=presentation localPrune coker symmetricToExteriorOverA(M,ee,xx)
fN3=res coker N
--fN3=(localResolution(coker N,LengthLimit=>2*d))[d-1]**E^{{d-1,d}}
bettiT dual fN3

M1=coker substitute(gens I2,S)
M=presentation localPrune (((ideal xx)^d)*M1)**S^{{0,d}}
N=presentation localPrune coker symmetricToExteriorOverA(M,ee,xx)
--fN2=(localResolution(coker N,LengthLimit=>2*d))[d-1]**E^{{d-1,d}}

fN2=res coker N
bettiT dual fN2
bettiT dual fN3


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













