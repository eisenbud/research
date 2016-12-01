restart
load "local.m2"
kk=ZZ/101
A1=kk[a,b,c,Degrees=>{3:{2,0}}]

I=ideal{a^3+b^3+c^3}
--The following  does not work yet because of non local compute tations
I=ideal{a*b*c+a^4+b^4+c^4}
A=A1/I
S1=kk[a,b,c,x_0,x_1,x_2,Degrees=>{3:{2,0},3:{1,1}}]

xx1=matrix{{x_0,x_1,x_2}}

S=S1/substitute(I,S1)
setMaxIdeal(ideal(a,b,c,x_0,x_1,x_2))
xx=substitute(xx1,S)
I2=minors(2,matrix{{a,x_0},{b,x_1},{c,x_2}})
--+ideal(x_0^3+x_1^3+x_2^3)
I3= saturate(I2,ideal(a,b,c))
-- try also I3=I2
transpose gens I3
M1=coker substitute(gens I3,S)
d=4
M=presentation localPrune (((ideal xx)^d)*M1)**S^{{0,d}}
E1=kk[a,b,c,e_0,e_1,e_2,Degrees=>{3:{2,0},3:{1,1}},SkewCommutative=>true]
E=E1/substitute(I,E1)
setMaxIdeal(ideal(a,b,c,e_0,e_1,e_2))
ee=matrix{{e_0,e_1,e_2}}
load "computingRpi_star.m2"
N=presentation localPrune coker symmetricToExteriorOverA(M,ee,xx)
fN=localResolution(coker N,LengthLimit=>2*d)[d-1]**E^{{d-1,d}}
bettiT dual fN
