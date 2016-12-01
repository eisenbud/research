--Versal deformation of the extension of direct sum of line bundles on P1

kk=ZZ/101
--For O(a1)+O(a2)+...+O(ad), a1<=...<=ad.
--The base ring of the versal deformation for (a)=(0,2).
A=kk[r_0,r_1, Degrees=>{{2,0},{2,0}}]
S=kk[join( gens A,{x_0,x_1}),Degrees=>join(apply(gens A,a->degree a),{2:{1,1}})]
E=kk[join( gens A,{e_0,e_1}),Degrees=>join(apply(gens A,a->degree a),{2:{1,1}}),SkewCommutative=>true]
ee=matrix{{e_0,e_1}}
use S
xx=matrix{{x_0,x_1}}

M= map(S^{{2,0},4:{0,0}}, S^{3:{-1,-1}},
matrix{{r_0*x_1, r_1*x_1,0},
        {x_0,0,0},
	{x_1, x_0, 0},
	{0,x_1,x_0},
	{0,0,x_1}})
isHomogeneous M
M2= (presentation prune (((ideal(x_0,x_1))^2)*(coker M)))**S^{{0,2}}


use E
N1=matrix{
     {e_0    ,e_1,0  ,0  ,0  , 0 ,0},
     {r_0*e_1,0  ,e_0,e_1,0  , 0 ,0},
     {r_1*e_1,0  , 0 ,e_0,e_1, 0 ,0},
     {0      ,0  , 0 ,0  ,e_0,e_1,0},
     {0      ,0  , 0 ,0  ,0  ,e_0,e_1}}

N=map(E^{{-2,0},4:{0,0}},E^{2:{-3,-1},5:{-1,-1}},N1)
betti N
transpose N
betti transpose N
isHomogeneous N
betti (fN=res( coker transpose N,LengthLimit=>10))
--bettiT (T=fN**E^{{0,3}})
--bettiT fN
--Rpi=degreeZeroPart(T,A)
--bettiT Rpi
--betti Rpi
-------------
--A=kk[r_0,s_0,t_0,u_0..u_2,v_0..v_2,w_0..w_4,Degrees=>{14:{2,0}}]