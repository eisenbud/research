restart
load "computingRpi_star.m2"
kk=ZZ/101
A=kk[y,z,Degrees=>{2:{2,0}}]
E=kk[e_0..e_3,y,z,Degrees=>{4:{1,1},2:{2,0}},SkewCommutative=>true]
ee=matrix{{e_0,e_1,e_2,e_3}}
S=kk[x_0..x_3,y,z,Degrees=>{4:{1,1},2:{2,0}}]
xx=matrix{{x_0..x_3}}
M=coker matrix{{y*x_1,z*x_2,x_3}}
d=5
betti(m1=presentation prune ((ideal(x_0,x_1,x_2,x_3))^d*M))
m1
m=m1**S^{{0,d}}
bettiT chainComplex m
n=symmetricToExteriorOverA(m,ee,xx)
fN=res(coker n,LengthLimit=>2*d-1)[d-1]**E^{{0,d}}
bettiT dual(fN)
diags=apply(-3..3,i->(
	  T=fN**E^{{0,i}}[i];
	  Rpi=degreeZeroPart(T,A)))

apply(diags,d->bettiT dual(d))	  
Rpi3=degreeZeroPart(fN**E^{{0,3}}[3],A)
bettiT dual(Rpi3)
Rpi3.dd_(-1)
Rpi3.dd_(-0)

fN.dd_0
fN.dd_(1)
transpose fN.dd_2|fN.dd_0
-------
e012=e_0*e_1*e_2
M=matrix{{0,0,0,e012},{0,0,e012,y*e_0*e_2},{0,e012,0,z*e_0*e_1},{e012,-y*e_0*e_2,z*e_0*e_1,e_0*y*z}}
N=map(E^{{-2,2},{-1,1},{-1,1},{0,0}},E^{{-3,-3},{-4,-2},{-4,-2},{-5,-1}},M)
isHomogeneous N
betti N
N
betti (fN=res coker N)
fN.dd_2
y*e_0-e_0*y

betti res coker vars E
N1=matrix{
 {e_0, 0 , 0 ,0,0,0,0,0,0},
 {e_1,e_0, 0 ,y,0,0,0,0,0},
 {e_2, 0 ,e_0,0,z,0,0,0,0},
 { 0 ,e_1, 0 ,0,0,y,0,0,0},
 { 0 ,e_2,e_1,0,0,0,y,z,0},
 { 0,  0 ,e_2,0,0,0,0,0,z}}
isHomogeneous N1
betti (fN1=res coker N1)     
betti fN
N2=fN1.dd_3
betti(N3=transpose N2**E^{{-9,-5}})
N3
time betti (hom=Hom(coker N2,coker N3))
time betti (homa=Hom(coker N2,coker N2))
betti (hom1=prune hom)
betti prune homa
N2
N2
N3
