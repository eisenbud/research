----
viewHelp Points
restart
loadPackage "Chi2"
loadPackage("Points", Reload=>true)
r = 3
I = randomPoints(r,8)
betti (F =  res I)
apply(r+1//2,p-> ann HH_(2*p+1)(sym2 F))
apply(r+1//2,p-> ann HH_(2*p)(wedge2 F))
ann HH_2 wedge2 F
S = ring I
phi =map(S,S,apply(numgens S, i->S_i^2))
J = phi I
F = res J
ann HH_2 wedge2 F

r=3
S = kk[x_0..x_r]
M = random(S^2, S^{4:-2})
I = minors (2,M)
betti(F= res I)
apply(r+1//2,p-> ann HH_(2*p+1)(sym2 F))
apply(r+1//2,p-> ann HH_(2*p)(wedge2 F))
H = prune HH_2 wedge2 F;
ann H
betti res H


r=5
S = kk[a_0..a_r]
I = monomialCurveIdeal(S,{4,5,6,7})
betti (F =  res I)
apply(r+1//2,p-> ann HH_(2*p+1)(sym2 F))
apply(r+1//2,p-> ann HH_(2*p)(wedge2 F))
T = Tor_2(S^1/I, S^1/I)
betti res T
H = prune HH_2 wedge2 F

r=3
S = kk[a_0..a_r]
I = (ideal vars S)^3
betti (F =  res I)
apply(r+1//2,p-> ann HH_(2*p+1)(sym2 F))
apply(r+1//2,p-> ann HH_(2*p)(wedge2 F))
