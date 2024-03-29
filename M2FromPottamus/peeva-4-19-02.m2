restart
--Project: list all the ideals (up to conjugacy) in small exterior algs, compute
--their invariants.
kk=ZZ/32003
E=kk[x,y,z,w,SkewCommutative=>true]
m=ideal vars E
--i=m^3+ k linear forms

tate20 = (m -> 
     betti res(transpose (res(m, LengthLimit=>8).dd_8)), LengthLimit=>16)

(res(m, LengthLimit=>8)).dd_8))

m=matrix{{x*y+z*w}}
tate20 m

betti res (coker matrix{{x*y+z*w}}, LengthLimit=>10)
betti res (coker matrix{{x*y}}, LengthLimit=>10)
betti res (coker matrix{{x*y, x*z}}, LengthLimit=>10) -- line in Grass
betti (res (coker matrix{{x*y+z*w, (x)*(z)}}, LengthLimit=>10) 
-- line meeting Grass, in tan plane
betti res (coker matrix{{x*y, z*w}}, LengthLimit=>10) -- two skew lines

betti res(coker matrix{{x*y+z*w, x*z, x*w}}, LengthLimit=>10) 
-- plane meeting G in 2 skew lines 
betti res(coker matrix{{x*y+z*w, x*z, y*w}}, LengthLimit=>10)
-- plane meeting G in nonsing conic

