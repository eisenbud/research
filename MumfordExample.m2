needsPackage "Points"
viewHelp Points
kk = ZZ/32003
P2 = kk[x,y,z]
mat = randomPointsMat(P2,6)
sub(mat, ZZ)
IN = (projectiveFatPoints(sub(mat, ZZ),{4,3,3,3,3,3},P2))_0
I = trim ideal (projectiveFatPoints(sub(mat, ZZ),{4,3,3,3,3,3},P2))_1
betti I
numgens IN
betti IN

