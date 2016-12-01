{*
Kloosterman's thm: if C is a nodal plane curve of degree d, then the last
syzygies of the ideal of the nodes are of degree at most d, and the number
of syz of degree = d is 1 less than the number of components.
*}

k=ZZ/101
S = k[x,y,z]

rat = method()
rat(ZZ) := d->(
     T = k[X,Y];
{*
     i = ker map(T,S, random(T^1,T^{3:-d}));
     diffs = ideal diff(vars S, gens i);
     time j = intersect decompose diffs;
     i = ker map(T,S, random(T^1,T^{3:-d}));
     diffs = ideal diff(vars S, gens i);
     time j= radical diffs;
*}
     i = ker map(T,S, random(T^1,T^{3:-d}));
     diffs = ideal diff(vars S, gens i);
     j = saturate diffs;
     assert(degree j == binomial(d-1,2));
     print betti res j;
     L=flatten degrees ((res diffs)_2);
     print(min L, max L)
     )

rat(List) := L ->(
     T = k[X,Y];
     i:= product(L, e->ker map(T,S, random(T^1,T^{3:-e})));
     diffs = ideal diff(vars S, gens i);
     j = saturate diffs;
     assert(degree j == binomial((sum L)-1,2)+#L-1);
     print betti res j;

     )


ell = method()
ell(ZZ) := d->(
     T = k[X,Y,Z]/ideal(Y^2*Z-X*(X-Z)*(X+Z));
     D = gens (ideal(X^d):((ideal(X,Y))^d));
     D2 = D*random(source D, T^{3:-d});
     i = ker map(T,S,D2);
     diffs = ideal diff(vars S, gens i);
     j = saturate diffs;
     assert(degree j == binomial(d-1,2)-1);
     print betti res j;
     L=flatten degrees ((res diffs)_2);
     print(min L, max L)
     )

pointsIdeal = method()
pointsIdeal Matrix := Q ->(
     T = ring Q;
     n = numgens T;
     P= Q|| matrix{{numcols Q:1}};
     print Q;
     intersect apply(numcols P, j->
	  ideal(apply(n-1, i-> P_j_(i+1)*T_0-P_j_0*T_(i+1))))
     )
pointsIdeal (Matrix, ZZ) := (Q,d) ->(
     T = ring Q;
     n = numgens T;
     P= Q|| matrix{{numcols Q:1}};
     print Q;
     intersect apply(numcols P, j->
	  (ideal(apply(n-1, i-> P_j_(i+1)*T_0-P_j_0*T_(i+1))))^d)
     )


end
restart
load "node-syzygies.m2"
n=3
T = kk[a_0..a_n]
P1 = id_(T^3)|transpose matrix{{n:1}}
--cols of P1 are the affine coords of the points.
pointsIdeal P1
betti res pointsIdeal (P1,2)
m1 = gens pointsIdeal (P1,2)
f =ideal(m1*random(source m1,T^{-3}))
source m1
degree oo

S = kk[x,y,z]
q1 = x^2+y^2+z^2
q2 = x^2+2*y^2+3*z^2
f = q1*q2
D =diff(vars S,gens ideal(f))
T = kk[x,y,z,A,B,C, Degrees => {1,1,1,3,3,3}]
DT =substitute(D,T)
I = ideal(matrix{{A,B,C}}-DT)+ideal(substitute (matrix{{f}}, T))
gauss = eliminate({A,B,C}, I)
decompose gauss
trim minors(1,syz D)
use S
(f*y*z) % gens gb ((ideal D)^2)
saturate ideal D == ideal(q1,q2)
J = ideal D
f% gens gb saturate (J^2)
trim((J^2):(intersect (saturate(J^2),J)))
betti res oo
viewHelp eliminate
viewHelp diff

ell 7
betti res diffs
rat 5     
time rat 10

time rat {2,3,5,7}
for d from 11 to 20 do time rat d
{*
This is always the syzygies of the d-2 power of the max ideal in 2 vars;
and the reason must be that (by Bezout) the nodes can never lie
on a curve of degree d-3.
*}

for d from 3 to 20 do(
     print d;
     time ell d)
	  
	  
S = kk[x,y,z]	  
M = random(S^{3:-6}, S^{-11, -7})
i = minors(2,M)
delta = saturate(i^2)
f = (gens delta) * random(source gens delta, S^{-11})
     diffs = ideal diff(vars S, f)
     j = saturate diffs;
degree j
     print betti res j;
     L=flatten degrees ((res diffs)_2);
     print(min L, max L)


