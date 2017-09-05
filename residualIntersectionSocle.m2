

end--
viewHelp genericMatrix
viewHelp isHomogeneous

restart
load"residualIntersectionSocle.m2"
kk= ZZ/101
S = kk[a,b,c]
random(S^3, S^{4:-2})
m = matrix"a2,b2,c2,bc ;bc, a2+c2,b2, bc ;ab,c2,a2,b2"
I = minors(3,m)
codim I

Jmat = (gens I)*random(source gens I, S^{3:-6})
J = ideal Jmat
J2 = ideal Jmat_{0,1}
K = J:I
K2 = J2:I
R = S/K2
f = map(R, S)
Omega = coker  map(R^3, , f jacobian K2)

Dtilde = diff(transpose vars S, Jmat)
Deltatilde = det Dtilde
D = diff(transpose (vars S)_{0,1}, Jmat_{0,1})
Delta = det D

ratio = gens ker(map( Omega, ,f diff(transpose vars S, Jmat_{2}))| Omega_{2})
del = matrix{{Deltatilde,Delta}}
del *ratio


{*$S=k[x,y]$,\ 
$F$ the sequence $x^{2}+y^{2}, x+y$ and $G=x$ we have
$$
(G^2F):\det \jacobian (GF) = (x),
$$
so $\det \jacobian(GF)$ is not in the socle modulo $(G^{2}F)$

should be I^t+1/JI^t. So must be J = GF, I = G=x t=1
*}
restart
S = QQ[x,y];
F = matrix"x2+y2, x+y";
F' = matrix"x2-xy,x+y";
T = QQ[x,y,z]
FT'' = (matrix"x2+y2,zx+zy")*random(T^{2:-2}, T^{2:-2})
dehom = map(S,T,{S_0,S_1,1_S})
F'' = dehom FT''
use S
G = x;
I = ideal G;
J = ideal (G*F)
J' = ideal (G*F')
J'' = ideal (G*F'')
J==J'

Jac = det jacobian (J) -- note: not even in I^2 = (x^2).
Jac' =det jacobian (J') -- is in I^2
Jac'' = det jacobian J''
I^2: Jac''

ideal (G^2*F):Jac -- = (x)
ideal (G^2*F):Jac' -- = (x,y)
(ideal(G^2*F) + ideal(G*F_{1})):Jac

G*F_{1}|G^2*F_{0}
R = S/ideal(G*F_{1}|G^2*F_{0})
g = map(R,S)
(ideal g(G^2*F)): ideal g Jac


restart
S = ZZ/101[x,y,z]
I = ideal x
J= ideal"xy,xz"
newvars = matrix"y,z,x+y+z"


restart
kk= ZZ/101
S = kk[a,b,c]
a1= a*(c-a-b)
a2= b*(c-a-b)
I = ideal(c-a-b)
(ideal a1):I
(ideal (a1,a2)):I


----
--Test whether Delta_s' \in I^{s'-g+1)*R_s' for g <= s' <= s.
restart
load"residualIntersectionSocle.m2"
kk= ZZ/101
S = kk[a,b,c,d,e]
vars1 = (vars S)*random(source vars S, source vars S)

m = random(S^2, S^{3:-1});
m = random(S^2, S^{3:-2});
I = minors(2,m);

mskew1 = random(S^5, S^{5:-1})
m = mskew1-transpose mskew1
I = pfaffians(4, m);

I = ideal random (2,S)
I = ideal random (3,S)
g = codim I
s = 5

Jmat = (gens I)*random(source gens I, S^{s:-2});
Jmat = (gens I)*random(source gens I, S^{s:-3});
Jmat = (gens I)*random(source gens I, S^{s:-4});
Jmat = (gens I)*random(source gens I, S^{s:-5});

--Now check the inclusion 

J = apply(s+1,s'-> Jmat_{0..s'-1});
K = apply(J, Ji -> (ideal Ji):I);
--check residual intersection codims
K/codim
assert(K/codim == toList(0..s))
--which are geometric?
apply(toList(g..s), s'->s'+1 == codim(I+K_s'))

Delta = apply(s+1, i-> det diff(transpose(vars1)_{0..i-1}, J_i));
R = apply(s+1, s' -> S/K_s');
toR = apply(s+1, s'->map(R_s', S));
Deltabar = apply(s+1, s'->toR_s'(Delta_s'));

apply(toList(g..s), j->(Deltabar_j)%toR_j(I^(j-g+1)) == 0)


----------------------
--canonical ideal of residual intersections
--151227 Conjecture: if the codim of some intermediate residual intersection is too large,
--then the map we construct I^{t+1}/JI^t \to \omega_{R/K} is the zero map.

restart
S = kk[a..h]
M = genericMatrix(S,a,2,4)
I = minors(2,M)
J = apply(7, s->ideal(gens I * random(source gens I, S^{s:-2})));
K = apply(7, s -> J_s:I);
K/codim
Q = I^5/(J_5*I^4);
prune Q

restart
S = kk[a..i]
M1 = S^{-1}**transpose genericMatrix(S,a,3,3)
M2 = transpose matrix"g,d,a;
h,b,e"
M2 = transpose matrix"g,d,a;
e,i,a"
M = M1|M2

I2 = minors(2, M)
codim I2

I = minors(3, M)
codim I
J7 = ideal(gens I * random(source gens I, S^{7:-3}))
K7 = J7:I
Q = I^5/(J7*I^4);
prune Q


J6 = ideal(gens I * random(source gens I, S^{6:-3}))
K6 = J6:I
codim K6

--------------

restart
S = kk[x_1..x_15]
M = genericMatrix(S,x_1,3,5)
I = minors(3, M)
codim I
J7 = ideal(gens I * random(source gens I, S^{7:-3}))
K7 = J7:I;
codim K7
J6 = ideal(gens I * random(source gens I, S^{6:-3}))
K6 = J6:I;
codim K6

----------------
--Example 2.10 from our paper:
restart
R = kk[x_1..x_10, Degrees =>toList(10..19)]
M = matrix{{x_1..x_10},{x_2..x_10,x_1^2}}
I = minors(2,M);
Rbar = R/I
L = ideal(x_1,x_2)
om = module L
OM = pushForward(map(Rbar,R),om)
betti res OM

(L^8):(L^4)==L^4
L' = ideal(x_1,x_2,x_4,x_5)
(L'^8)==(L')^8
(L'^8):(L')^4 == L'^4
L^4 == L'^4
L'' = ideal(x_1,x_2,x_5)
(L'^8):(L'')^4 == L''^4


----
Checking some examples
R = ZZ[x,y]
F = matrix"x2+y2,x+y"
F' = matrix"x2-xy,x+y"
G = x
det jacobian F*G
D = det jacobian (F'*G)
D%ideal (G^2*F)
gens (D*ideal(x,y))%ideal (G^2*F)


---
{*$(a_{1}, \dots, a_{d}) = (a_{1}',\dots, a_{d}')$, then the Jacobian determinants
of $a_{1}, \dots, a_{d}$ and $a_{1}',\dots, a_{d}'$ differ by an element of the ideal
$$
J\cdot I_{d-1}(\jacobian(a_{1}, \dots, a_{d})),
$$
where $I_{d-1}(\jacobian(a_{1}, \dots, a_{d}))$ denotes the ideal of $(d-1)\times (d-1)$ minors of the
Jacobian matrix. 
*}

S = ZZ/101[x,y,z]
A = random(S^1,S^{-2,-3,-4})
g = random(source A, source A)
A' = A*g
delta = det (jacobian A) - det(jacobian A')
J = ideal A
I = (J* minors(2, jacobian A))+J^2*minors(1, jacobian A)
delta % I

{*
Let $R=k[x,y]$, where $k$ is a field of characteristic $\neq3$, and take $I= (G)$ with $G=x^{2}+y^{2}$, 
and $F = x,y$. If we replace the Jacobian matrix
$\jacobian(GF)$ by
$$
A :=\frac{1}{3}\jacobian(GF) +
\begin{pmatrix}
 -y&x\\
 -y&x
\end{pmatrix}
$$
then
$$
A
\begin{pmatrix}
 x\\y
\end{pmatrix} =
\begin{pmatrix}
 GF_{1}\\GF_{2}
\end{pmatrix}
$$
but
$\det(A) = G$; in particular it is in $I$ but not in the socle of $I/JI$.
*}
S = ZZ[x,y]
G = x^2+y^2
G = x*y
F =  matrix"x,y"
J =jacobian(G*F)
M = matrix"-y,x;
-y,x"
(D = det(A = J+M)) %G
A*transpose vars S
transpose (G*F)
gens(ideal(x,y)*D)%(G^2*F)
