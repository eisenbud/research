E = kk[a,b,c,d,SkewCommutative => true]
phi = map(E^1, E^{-3,-1}, matrix"ab,d")
F = res coker phi
G = dual F
for i from -4 to -1 do print (0== G.dd_i*G.dd_(i+1))
