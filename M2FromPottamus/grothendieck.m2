restart
A=kk[e,f,t,Degrees=>{1,1,2},SkewCommutative=>true]
phi=map(A^4,A^{-1,-1,-2},matrix{{e,0,0},{f,e,0},{0,f,0},{0,t*e, e*f}})
load "local.m2"
setMaxIdeal ideal (e,f,t-1)
betti(F= localResolution (coker phi))

betti(G= localResolution (coker transpose phi,LengthLimit=>7))
F.dd_2
F.dd_4
M=(coker transpose  F.dd_4)
localResolution M
localsyz (transpose F.dd_4)

localComplement F.dd_3
localsyz phi
