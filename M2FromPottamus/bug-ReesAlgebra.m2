restart
loadPackage "Snowbird/ReesAlgebra"
loadPackage "ReesAlgebra"
load "ReesAlgebra-v01.m2"
S=kk[x,y]
i=ideal"x5,y5, x3y2"

iR = reesIdeal(i,i_0)

betti res iR 
loadedPackages

restart
load "ReesAlgebra-v01.m2"
S=kk[x,y]
i=ideal"x5,y5, x3y2"

iR = reesIdeal(i)
iR = reesIdeal(i, Strategy=>Saturate)
betti res iR 
degrees vars ring iR
describe ring iR
use S
T=S/(ideal"x7y7")
I=ideal"x5,y5, x3y2"
iR = reesIdeal(I)

R = QQ[x,y,z]/ideal(x*y^2-z^9)
J = ideal(x,y,z)

R = QQ[x,y,z],
I = ideal(x*y^2-z^9),
J = ideal(x,y,z),
symmetricKernel(gens J)

