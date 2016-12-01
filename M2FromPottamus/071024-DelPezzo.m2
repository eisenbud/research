--del Pezzo surface with one singular point of type A4 (right singularity?)
--the following is the result of blowing up the plane at a point and three
--infinitely near points, the last on the third exceptional divisor,
--but not its intersection with the original flex line:
--ideal of cubics meeting a given smooth cubic >=4 times
--at its flex point, (and with same flex tangent.)

---------
restart
kk=ZZ/32003
S=kk[x,y,z]
--cubics with flex tangent x=0 at x=y=0 AND meeting x=t^3, y=t 4 times there:
i=ideal"x3,x2y,x2z,xy2,xyz,xz2-y3"
G=gens i
T=kk[a..f]
K=kernel map(S,T,G) -- ideal of the del Pezzo
betti (KK=res K) -- yes, a degree 5 del Pezzo
--compute the singular locus:
JK=jacobian K
sing=minors(3,JK)+K
codim sing -- 5
degree sing -- 4
decompose sing -- One singular point only.

KK.dd_3
transpose KK.dd_1
M0=(KK.dd_2)_{4,3,2,1,0}
p=map(T^1,T^1, matrix{{1_T}})
P=p++p++-p++p++p
M=P*M0
0==M+transpose M
M
N0=matrix"0,a,b,c,d;
       0,0,c,d,e;
       0,0,0,e,0;
       0,0,0,0,f;
       0,0,0,0,0"
N=N0-transpose N0
k=ideal transpose (res coker N).dd_2
Jk=jacobian k
singj=minors(3, Jk)+k
codim singj
degree singj
decompose singj

K1=substitute(K, {f=>1})
U=kk[c,d,e]
viewHelp eliminate
Ksing=eliminate({a,b},K1)
F=map(U,T, matrix{{c^2+(d^2-c*e)*d, d^2-c*e, c,d,e,1}} )
F(K1)
KSS=Ksing+ideal jacobian Ksing
degree KSS
--Is this the same?
N0=matrix"0,a,b,c,d;
       0,0,c,d,e;
       0,0,0,e,b;
       0,0,0,0,f;
       0,0,0,0,0"
N=N0-transpose N0
k=ideal transpose (res coker N).dd_2
Jk=jacobian k
singj=minors(3, Jk)+k
codim singj -- it's smooth
degree singj
decompose singj


------------------
--the following is the result of blowing up the plane at a point and two
--infinitely near points, corresonding to the ideal of cubics with given
--flex point and flex tangent, and passing through one more point.
--THIS HAS TWO SINGULAR POINTS

restart
kk=ZZ/32003
S=kk[x,y,z]
i=x*(ideal(x,y,z))^2+ideal y^3 -- cubics meeting x=0 3 times at y=0.
j=ideal(y,z) -- point (1,0,0)
G=gens intersect(i,j)
T=kk[a..f]
K=kernel map(S,T,G) -- ideal of the del Pezzo
betti (KK=res K) -- yes, a degree 5 del Pezzo
--compute the singular locus:
JK=jacobian K
sing=minors(3,JK)+K
codim sing -- 5
degree sing -- 3
decompose sing -- seems to have TWO singular points.

KK.dd_2
---------------

--Now cubics tangent to a line at one point and with one more fixed point on
--the line, as well as another far away base point.
--kk=ZZ/32003
restart
S=kk[x,y,z]
i=x*(ideal(x,y,z))^2+ideal"y2z" -- cubics meeting x=0 2 times at y=0, 1 time at z=0
j=ideal(y,z) -- point (1,0,0)
G=gens intersect(i,j)
T=kk[a..f]
K=kernel map(S,T,G) -- ideal of the del Pezzo
betti (KK=res K) -- yes, a degree 5 del Pezzo
--compute the singular locus:
JK=jacobian K
sing=minors(3,JK)+K
codim sing -- 5
degree sing -- 2
decompose sing -- again seems to have TWO singular points.

KK.dd_2

