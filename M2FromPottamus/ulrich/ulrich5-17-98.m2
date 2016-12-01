kk=ZZ/32003
R=kk[a..d]
m=ideal vars R
i=ideal(a)
f=random(R^1,R^{-1,-1,-1})
j=ideal((gens i^2)*f)
betti j
J=saturate(j,i) -- 3 random linear forms
----------------
restart
kk=ZZ/32003
R=kk[a..e]
i=ideal(a,b)
f=random(R^3,R^{0,0,-1}) -- get the unit ideal from the sat below
f=random(R^3,R^{0,-1,-1})
-- in 4 vars, the saturation is a 1,1,2 complete int
-- in 5 vars the sat is perf, codim 3, deg 2, ideal contains 1 lin form
--(2 skew lines)
f=random(R^3,R^{-1,-1,-1})
-- in 4 vars the sat is perfect, codim 3, deg 7
-- in 5 vars sat is imperf, unmixed, codim 3, deg 7
j=ideal((gens i^2)*f)
J=saturate(j,i)
betti res J
codim J
degree J
dim Ext^4(R^1/J,R)
--------------------
restart
kk=ZZ/32003
R=kk[a..e]
i=monomialCurve(R,{1,2,3})
f=random(R^6,R^{0,0,-1}) -- sat is imperfect but unmixed, of codim 4
f=random(R^6,R^{0,-1,-1})--  sat is imperfect but unmixed, of codim 4
f=random(R^6,R^{-1,-1,-1})--  sat is imperfect but unmixed, of codim 4
j=ideal((gens i^2)*f)
--betti res j
J=saturate(j,i)
betti res J
codim J
degree J
dim Ext^4(R^1/J, R)
----------------------
restart
kk=ZZ/32003
R=kk[a..e]
i=ideal(a,b,c)
f=random(R^6,R^{0,0,0,-1}) -- get the unit ideal from the sat below
f=random(R^6,R^{-1,-1,-1,-1})-- the saturation is perf, codim 4, deg 33
f=random(R^6,R^{-2,-1,-1,-1})-- the sat is perf, codim 4, deg 52
j=ideal((gens i^2)*f)
J=saturate(j,i)
codim J
betti res J
degree J
-----------------
restart
kk=ZZ/32003
R=kk[a..f]
M=genericSymmetricMatrix(R,a,3)
i=ideal(mingens minors(2,M))
i2=ideal mingens ((i^2)+(minors(3,M)))
betti i2
f=random(source gens i2,R^{4:-4}) 
betti f
j=ideal ((gens i2)*f)
betti j
J=saturate(j, i^[2])





