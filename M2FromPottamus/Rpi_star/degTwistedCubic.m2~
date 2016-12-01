restart
load "local.m2"
kk=ZZ/101
A=kk[a,Degrees=>{1:{2,0}}]
S=kk[a,x_0..x_3,Degrees=>{1:{2,0},4:{1,1}}]
setMaxIdeal(ideal(a,x_0,x_1,x_2,x_3))
m=matrix{{a*x_0,x_3,x_1},{x_3,a*(x_1-x_0),x_2}}
I=minors(2,m)
J=saturate(I,ideal(a))
transpose presentation  localPrune coker gens J 
J1=ideal((gens J)_{1,2,4})
localsyz gens J1
M=S^1/J1
load "computingRpi_star.m2"

xx=matrix{{x_0..x_3}}
E=kk[a,e_0..e_3,Degrees=>{1:{2,0},4:{1,1}},SkewCommutative=>true]
ee=matrix{{e_0..e_3}}
setMaxIdeal(ideal(a,e_0,e_1,e_2,e_3))
d=7
m=presentation prune(((ideal xx)^d)*M**S^{{d,d}});
N=localPrune coker symmetricToExteriorOverA(m,ee,xx);
fN=localResolution( N,LengthLimit=>2*d)[d-1]**E^{{0,d}} 
bettiT dual fN
NN=fN.dd_0*directSum(matrix{{2_E}},matrix{{2_E}},id_(E^3))
BB=-NN^{4}||NN^{1}-a*e_3*NN^{4}||NN^{2}+NN^{1}-e_2*NN^{4}||-NN^{3}+e_0*NN^{4}||NN^{0}
B=BB_{0}|BB_{1}|BB_{2}-BB_{3}|BB_{3}|BB_{4}
C=B_{0,1}|B_{2}-a*e_3*B_{1}|B_{3,4}
--fC=localResolution image C
--bettiT dual fC 
Rpis1=apply(-4..5,i->(degreeZeroPart(fN[i]**E^{{0,i}},A)))
apply(Rpis1,c->bettiT dual c)
(Rpis1#9).dd_(-1)
