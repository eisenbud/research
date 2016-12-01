-- Some bugs having to do with exterior algebra code. 
-- last modified 12/15/98
produced with:
o6 = HashTable{VERSION => 0.8.48                   }
               architecture => i586
               compile node name => geometry
               compile time => Dec 11 1998 10:56:40
               dumpdata => true
               factory => true
               factory version => 1.2c
               gc version => 4.13 alpha 2
               libfac version => 0.3.1
               mp => false
               operating system => Linux
               operating system release => 2.1.131

------------------------------------------------

restart
kk=ZZ/32003
R=kk[x,y,z,SkewCommutative=>true]
p1=matrix{{x,0}}
H=res(coker p1, LengthLimit=>2)
betti H
--segmentation fault
-------------------------------------------


restart
kk=ZZ/32003
S=kk[a,b,c,d]
m=map(S^2,S^{-1,-1},matrix{{a,b},{c,d}})
jm=jacobian m
mt = transpose jm
jn=gens kernel mt
R=kk[A,B,C,D,SkewCommutative=>true]
ev=map(R,S,matrix{{A,B,C,D}})
JN = ev jn
q=vars(R)**id_(R^2)
p=q*JN
--The following line uses up all the memory; on my 64Mb machine
--it begins swapping, doesn't finish before I give up.
F=res(coker p, LengthLimit=>2)
--Same thing with larger LengthLimits
--however if I do
p1=gens kernel p
p2=gens kernel p1
--I get the answer almost instantaneously.

----------------------------------------------

kk=ZZ/101
R=kk[a,b,c,SkewCommutative=>true]
m=map(R^{-1,0},R^{-2,-1},matrix{{a,0},{b*c,a}})
betti m
F=res(coker m, LengthLimit=>5)
betti F
-- F is a minimal resolution. But:
--Bug: the following gives the wrong answer (a nonmin presentation)
prune coker (F.dd)_2

--------------------------------
restart
kk=ZZ/101
R=kk[x,y,u,v,SkewCommutative=>true]
i=ideal(x+u*v)
M=coker gens i
F=res(M, LengthLimit=>5)
(F.dd)_2
--The following command causes the system to hang
presentation (image(F.dd)_2/((ideal vars R)*(image(F.dd)_2)))

---------------------------

--Bug, sort of
--the exterior algebra is local; so m2 should compute
--MINIMAL resolutions over it EVEN in the inhomogeneous case! 
--But at the moment it does not
--as in the following example 
--(also mingens, prune fail to minimize correctly)


-------------------------------------
restart
kk=ZZ/101
R=kk[a,x,y,u,v,SkewCommutative=>true]
i=ideal(a+x*y+u*v)
M = R^1
j= ideal(0_R) : i
---bug
j1= (ideal(0_R) : i)*M
j2= (ideal(0_R) : j)*M
-- Shouldn't the following reduce one module mod the other?
j1 % j1
--gives an error msg







