R = ZZ/101[a,b,c,d]
N = mutableMatrix"
a,b,c,d,0,0,0;
0,a,b,0,d,0,0;
0,0,a,b,c,d,0;
0,0,0,a,b,c,d"

M = mutableMatrix N
M_(1,0)=c
M_(1,6) = c
codim minors (4,matrix M)

R = ZZ/101[a,b,c,d,e]
N = mutableMatrix matrix"
a,b,c,d,e,0,0,0,0;
0,a,b,0,0,e,0,0,0;
0,0,a,b,0,d,e,0,0;
0,0,0,a,b,c,d,e,0;
0,0,0,0,a,b,c,d,e"

N_(1,0) = 5*d;  N_(1,8)=3*d
N_(1,8) = d

N_(1,4) = 0
N_(2,0)= c+91*d
N_(1,7) = c+13*d ; 
N_(2,8) = 3*c+21*d
N_(1,0) = c+11*d
N_(1,8) = 7*d
N_(1,6) = 17*d
N_(2,7) = 25*d
N_(0,5)= 47*d
N
codim minors (5,matrix N)

R = ZZ/101[a,b,c,d,e,f]
N = mutableMatrix matrix"
a,b,c,d,e,f,0,0,0,0,0;
e,a,b,0,0,0,f,0,c,d,e;
d,0,a,b,0,0,e,f,0,c,d;
c,0,0,a,b,0,d,e,f,0,c;
0,0,0,0,a,b,c,d,e,f,0;
0,0,0,0,0,a,b,c,d,e,f"
N
codim minors (6,matrix N)


specialMat = (R,s,w) ->(
M1 = map(R^(s-1), R^{s-1:-1}, (i,j) -> 
    if i>=j and i-j< w then R_(i-j) else 0_R);
M1||matrix{{R_1..R_(s-1)}})

s = 6;w = 2;
R = kk[x_0..x_(s-1)]
M = specialMat(R,s,w)


I = minors(s-1, M)
for j from 1 to s-1 list codim minors (s-j, M)
G1 = gens minors(s-1, M)    
G1list = flatten entries G1
--J = sum(s,j->ideal(R_(s-1-j)*G1list_j))
--J = ideal(R_0*G1list_0)+ideal G1list_{1..s-1}
--codim(J: I )

J = ideal( gens I *random(source gens I, R^{s:-s}))
codim(J:I)

for j from 1 to (s-1)//2 do(
    <<j<<" "<<s-1-j<<endl;
    << betti res prune(I^j/(J*I^(j-1)))<<endl<<endl;
    << betti res prune (I^(s-1-j)/(J*I^(s-2-j)))<<endl<<endl<<endl;
	)



viewHelp MutableMatrix
N1 = matrix{{c}}**random(R^4, R^{0,1,1,1,1,1,0})
codim minors(4,N+N1)

codim minors(4,N)




M =matrix"a,b,0,0,0;
0,0,b,0,a;
0,0,a,b,0;
0,0,0,a,b"
codim minors (4,M)


restart
Example 6.1 in the 2017 version of the paper
--An s-residual intersection that is G_{w-1} but not G_{w}
macaulayMat= (R,s)->(
     map(R^(s), R^{2*s-1:-1}, (i,j) -> 
    if i<=j and i>=j-s+1 then R_(j-i) else 0_R)
)


g=2; s = 5; v=1; w = v+2; t=s-g; --max(1, (t-1)/2) <=v<=t in the theorem
--note that this is empty if s<5;
-and if s<=7 only v=1, w=3 is in question

-- we claim to have checked this for all admissible values 
-- of v and s <=7. The computation of the residual intersection becomes
--very slow from s=7, w=4 on (that is, all the cases s=7 (we allow w=4,5,6).
-- we have checked that it's an s-residual int in the case 7,4, not the others.

--Better to only do the cases s<=6 for the moment.

time for s from 5 to 6 do (for v from max(1,ceiling ((s-3)/2)) to s-2 do(
w = v+2;
--make an s x (s-1) matrix N whose 
--ideal of (s-1)-minors I satisfies G_w, not G_{w-1}:
<<(s,w)<<endl;
kk = ZZ/101;
R = kk[x_0..x_(s-1)];
M' = mutableMatrix (M= macaulayMat(R,s));
N' = M'_(toList(1..s-1));
N'_(s-w,s-2) = 0;
N = matrix N';
I = minors(s-1,N) ;
assert (codim I ==2);
codims = apply(s-1, j -> codim minors(s-1-j,N));
GinftyCodims = toList(2..s);
codims - GinftyCodims;
print (min positions(codims-GinftyCodims, i-> i<0) == w-2);
-- this proves: I is codim 2 and satifies G_(w-1) but not G_{w}.
M' = mutableMatrix (M= macaulayMat(R,s));
M'_(s-w,s-1) = 0;
M'_(s-w,0) = M'_(s-w,0)+ R_(w-1) ; -- replaced 1 by 0
M'_(s-w,2*s-w) = R_(w-1) ;
M' = matrix M';
--M'
--print(codim minors(s,M') == s);
--shows that the maximal minors of M' are codim s
--M' is (s-1) x (2*s-2); maximal minors are the (s-1) power of ideal vars S
colList = {0}|toList(s..2*s-2);
P = M'_colList;
J = ideal(transpose(syz transpose N)*P);
<<"special choice of J"<<endl;
--print(codim(K = (J:I)) == s);
--this shows that K is an s-residual intersection. The computation gets slow from (7,4) on.
--checked up to hear for s<=6 in 15 sec on old mac pro.
--
--
--Up to here we have shown that 
--the hypothesis of theorem 2.6 are satisfied EXCEPT for G_(w).
--
--Ns = gens minors(s-1,N);
--<<"general choice of J"<<endl;
--J = ideal(Ns*random(source Ns, R^{s:-s} ));
--print(codim(K = (J:I)) == s)
--this shows that K is an s-residual intersection in this generic case, too. 
--The computation gets slow from (7,4) on.
--
--Test duality:
for u from t-v to min(1+v,(s-1)//2) do(
    <<u<<" "<<s-1-u<<endl;
    << betti res prune(I^u/(J*I^(u-1)))<<endl<<endl;
    << betti res prune (I^(s-1-u)/(J*I^(s-2-u)))<<endl<<endl<<endl;
	)
))

{*In case s=5,w=2,  item (2) fails for u=2 because I^2/JI is NOT self-dual, as seen from the
resolution.
*}

--general J, with I computed above for s=5, w=2
J = ideal(gens I*random(source gens I, R^{s:-5}))
codim(J:I)
for j from 1 to (s-1)//2 do(
    <<j<<" "<<s-1-j<<endl;
    << betti res prune(I^j/(J*I^(j-1)))<<endl<<endl;
    << betti res prune (I^(s-1-j)/(J*I^(s-2-j)))<<endl<<endl<<endl;
	)
    
--general J, s=6
s=6
J = ideal(gens I*random(source gens I, R^{s:-5}));
codim(K=(J:I));
for j from 1 to (s-1)//2 do(
    <<j<<" "<<s-1-j<<endl;
    << betti res prune(I^j/(J*I^(j-1)))<<endl<<endl;
    << betti res prune (I^(s-1-j)/(J*I^(s-2-j)))<<endl<<endl<<endl;
	)
    
codim K
numgens ring I
    
S = kk[a,b,c,d,e]
m = matrix"a,b,c,d;
b,c,d,e"
I = trim minors (2,m)
betti res (I^2)

S = kk[a,b,c,d,e,f]
m = matrix"
    a,b,c;
    b,d,e;
    c,e,f"

S = kk[a,b,c,d,e,f,g,h]
m = matrix"
a,b,c,d;
e,f,g,h"

I = trim minors (2,m)
J = ideal ((gens I)*random(source gens I, S^{5:-3}))
betti res prune (I/J)
betti res prune (I^2/(J*I))

betti res (I^2)

H1 = (kernel koszul(1, gens I))/(image koszul(2, gens I))
betti res prune H1

H2 = (kernel koszul(2, gens I))/(image koszul(3, gens I))
betti res prune H2

H3 = (kernel koszul(3, gens I))/(image koszul(4, gens I));
betti res prune H3


m= 4
n=2
r=n-1

T = kk[z_{0,0}..z_{m-1,r}]
M = map(T^m, T^{n:-1}, transpose genericMatrix(T,T_0,n,m))
K = minors(r+1,M)
M' = M^{m-r..m-1}
I = minors(r,M')
J = ideal (reverse flatten entries gens minors(r+1,M))_{0..m-r-1}
K == (J:I)

R = kk[a,b,c]
M = mutableMatrix matrix"
b,a,0,0,0;
0,b,a,c,0;
0,0,b,a,c"
M_(2,0)=c
M_(0,4) = c
m = matrix M
codim (K= minors (3,m))
n = m_{0,3,4}
m1 = m_{1,2}
I = minors(2,m1)
m' = m_{0,3,4,1,2}
J = ideal( (flatten entries gens minors(3,m'))_{7,8,9})
trim J:I
codim(J:I)
middle = coker m
hf(-1..10, middle)
hf(0..10,R^1/K)
omega2 = prune Ext^3(R^1/K,R^{-5})
H = Hom(middle ** middle, omega2);

hf(0..10, prune (I^2/(I*J)))
basis(0,H)

f = homomorphism basis(0,H)
prune coker f
presentation middle
t = matrix"a,b,c"
t**t
reln = (syz(t**t))_{0,1,2}
prune coker map(middle**middle, R^3, reln)
f*map(source f, R^3, reln)
betti f


(gens intersect(I,(I*J:I)))%J
prune(I/J)
dua = R^{-4}**prune Hom((I/J), omega2)
homomorphism basis (0,Hom(dua,I/J))

hf(0..5, I/J)

------
--140530-Question about generation of the socle: when s=d
--should we conj that the socle mod I^{d-g}J is generated by
--any determinant of a matrix A such that 
--(x)A = f

--case g=1: notation as in prop. 6.4:
kk = ZZ/101
S= kk[a,b,c,d]

G = ideal"a5+b5+c5+d5"
F = ideal"a3,b3,c3,d3"

J= F*G
A = diff(transpose vars S, gens I)
8*(gens (F*G))==(vars S)*A

B = transpose koszul(2,vars S)
C = random(S^4, S^{6:-6})
D = C*B;
t = (J*(G^3)):ideal(det(D+A))
t = (J*(G^3)):ideal(det A)

restart
kk = ZZ/101
S= kk[a,b]

G = ideal"a5+b5"
F = ideal"a3,b3"

J= F*G
A = diff(transpose vars S, gens J)
8*(gens (F*G))==(vars S)*A

B = transpose koszul(2,vars S)
C = random(S^2, S^{1:-6})
D = C*B;
t = (J*(G)):ideal(det(D+A))
t = (J*(G)):ideal(det A)

restart

kk = ZZ/101
S= kk[a,b]

p= 2
q = 1
G = ideal(a^p+b^p) -- with this G, the det of the deformed Jacobian A+D is equal to G!
G = ideal(a*b) -- with this G the det of the deformed Jacobian A+D is  not in (G).
F = ideal(a^q,b^q)

J= F*G
A = diff(transpose vars S, gens J)

B = transpose koszul(2,vars S)
C = map(S^2, S^{1:-(p-2)},matrix{{a^(p-2)},{b^(p-2)}})
D = C*B;
t = (J*(G)):ideal(det(D+A))
det(D+A)%G
t = (J*(G)):ideal(det A)

K = res coker vars S
KJ = chainComplex (koszul(1, gens J), koszul(2, gens J))
KJ.dd_1*KJ.dd_2
m=map(KJ_0,K_0,(gens(G^2*F))_{1})
mm = extend(KJ,K,m, Verify=>true)

HH_1(mm)
mm

sigma1 = mm_0%(KJ.dd_1)
sigma1 = mm_0//(KJ.dd_1)
(mm_1-sigma1*(K.dd_1))
(mm_1-sigma1*(K.dd_1))//(KJ.dd_2)


-------------

S = kk[a,b,c,d,e]
rnc = matrix"a,b,c,d;
b,c,d,e"
I = minors(2, rnc)
J=ideal ((gens I)*random(source gens I, S^{4:-3}));
K = J:I;
betti res K
codim K
omega = prune Ext^4(S^1/K, S^{-5});
betti res omega
M = prune (I^2/(J*I))
betti res M
betti res omega
betti res I
viewHelp isSurjective

betti res (I^2)


----
--When is the Jacobian of GF the socle of I^2/IJ in the case t=1. Work in grade 1, I = G, J = GF where F is a regular seq
--of length s.
restart
S = kk[a,b]
f = 3
f1 = 4
g = 5
G = (flatten entries random(S^1, S^{-g}))_0
F2 = (flatten entries random(S^1, S^{-f1}))_0
F1 = (flatten entries random(S^1, S^{-f}))_0

G = a
F0 = a^2+b^2
F2 = a+b
F1 = (3*a+5*b)*(a+b) +F0

restart
--general choice doesn't give socle
S = kk[a,b]
G = a
F0 = a^2+b^2
F2 = a+b
F1 = (3*a+5*b)*F2 +F0
F1 = -b*(F2)+F0
codim ideal(F1,F2)

J = ideal(G*F1, G*F2)
JGF =det diff(transpose vars S, matrix{{G*F1,G*F2}})
JI = G*J
JI:ideal(JGF)

JGF%matrix{{G}}

G^2*JF%(gb i)
JGF%(gb i)


i = ideal(G^2*F1, G^2*F2)
j1=i+ideal(JGF)
j2=i+ideal(G^2*JF)
j1:j2
j2:j1
betti res i

----

S = kk[a,b,c]
mm=ideal vars S
I = ideal"a3, b5"
J1 = ideal((gens I)*random(source gens I, S^{1:-6}))
J = J1+ ideal(a^3*c^3,a^6+b^5*c)
codim(J:I)
d = det jacobian gens J
(I*J):d

-----

--g=2, t=1
restart
S= kk[a,b,c]
m = random(S^3, S^{2:-1, 2:-2})
I = minors(3,m)
codim I
codim minors(2,m)
Jmat = (gens I)*random(source gens I, S^{1:-5,2:-6});
J= ideal Jmat
d = det jacobian Jmat
(I*J):d



--g=2, t=2
restart
S= kk[a,b,c,d]
m = random(S^4, S^{3:-1, 2:-2})
I = minors(4,m)
codim I
codim minors(2,m)

Jmat = (gens I)*random(source gens I, S^{4:-7});

J= ideal Jmat

d = det jacobian Jmat
(I^2*J):d


--g=t=1 again
restart
S = kk[a,b]
G = a
I = ideal G
F1 = a^2+b^2
F2 = a+b
J = ideal(G*F1, G*F2)
s1= (3*a^2+b^2)*(a-b)
s = (2*a+b)*(3*a^2-b^2+2*a*b)
(I*J):s


--g=2, t=1
restart
R = QQ[x,y,z, Degrees =>{2,3,4}]
g = (x^2-z)
h = (x*z-y^2)
f = g*h
isHomogeneous f
J = diff(vars R,f)
I = saturate ideal J 
J' = J*(id_(source J) + matrix"0,0,0;0,0,0;7x,0,0")
hessf = det jacobian J
hessf'= det jacobian J'
hessf % gens(I^2)
hessf'% gens(I^2)

assert (I == (I*J): hessf)

assert( 0 != hessf % gens (ideal(J)*minors(2, jacobian J)+I^2))
isHomogeneous(ideal(J)*minors(2, jacobian J)+I^2)

assert(I == ideal (g,h))

J2 = intersect(I^2+ideal J_{0,1},I^2+ideal J_{0,2},I^2+ideal J_{1,2})
trim J2
hessf % gens(I^2+ ideal(gens J2 % (I^2)))
toList(0..2)-set{1}

J' = map(R^1, source gens J, gens J)*random(source gens J, R^{3:-12})
isHomogeneous J'
I == saturate ideal J'
s = det jacobian J'
s% gens(I^2)
s% gens(I*ideal J')
I*(ideal J') : ideal s

 ----- Same computation with random g,h
restart
R = QQ[x,y,z, Degrees =>{2,3,4}]

g = random(R^1, R^{-4})
h = random(R^1, R^{-6})
f = g*h
isHomogeneous f
J = ideal diff(vars R,f)
hessf = det jacobian J
codim J
I = saturate J 
degrees gens I
hessf % gens(I^2)
(I*J):hessf
I == radical I

J' = map(R^1, source gens J, gens J)*random(source gens J, R^{3:-12})
isHomogeneous J'
I == saturate ideal J'
s = det jacobian J'
s% gens(I^2)
s% gens(I*ideal J')
I*(ideal J') : ideal s


---Evidence to suggest that if J generated by elements of the same quasihomogeneous degree, then
--the socle theorem holds as in the homogeneous case.
restart
R = QQ[x,y,z, Degrees =>{2,3,4}]

I = ideal (random(R^1, R^{-10,-12}))
J' = map(R^1, source gens I, gens I)*random(source gens I, R^{3:-24})
isHomogeneous J'
I == saturate ideal J'
s = det jacobian J'
s% gens(I^2)
s% gens(I*ideal J')
I*(ideal J') : ideal s


---Which elements do give Jacobian in I^t+1
--g=t=1 again
restart
S = kk[a,b]
G = a
I = ideal G
F1 = a^2+b^2
F2 = a+b
J = matrix{{G*F1, G*F2}}
det jacobian J % ideal(G^2)
J' = matrix{{G*F1+(5*a+13*b)*G*F2, G*F2}}
J' = matrix{{G*F1+(6*a-b)*G*F2, G*F2}}
det jacobian J' % ideal(G^2)

a1 = J_{0}
a2 = J_{1}
gens (intersect(ideal a1 + I^2, ideal a2+I^2))%(I^2)


restart
R = QQ[x,y,z, Degrees => {2,3,4}]
f = (x^2-z)*(x*z-y^2)
assert isHomogeneous f
J = ideal diff (vars R, f)
I = top J
assert(codim J == 2)
Hess = diff(transpose vars R, diff (vars R, f));
sing = J+minors(2, Hess);
assert(codim sing == 3)
hess = det Hess
assert(0 != hess % gens (J*minors(2, Hess)+I^2))

----
Nonreduced examples:

R = kk[a,b,c]
II = apply(2, i -> ideal random(R^1, R^{-3}))
II = {ideal"a3", ideal"b3"}
II = {ideal"a2", ideal"ac-b2"}
I = II_0^2 + II_1^2
J = (gens I) *random(source gens I, R^{3:-7});
D = det jacobian J;
D % gens(I^2)

----
--Example 6.5 of the 170305 version: Duality not given by multiplication.

restart
S = ZZ/101[x,y,z]
I = (ideal(x,y))^2
Jm= (gens I)*random(source gens I, S^{3:-3});
J = J3 = ideal Jm;
J1 = ideal J_0
J2 = ideal(Jm_{0,1});
K1 = J1:I 
assert (K1 == J1)
K2 = J2:I
K3 = J3:I

--the following assertions check the hypotheses of Thm 4.1
assert(codim K2 == 2)
assert(codim K3 == 3)
assert(codim((K1+ideal(J_1)):I) == 2)
assert(codim((K2+ideal(J_2)):I) == 3)
assert(codim(I + K2) ==2)
assert(codim(I+K3) == 3)

--
apply(toList(-3..1), i->hilbertFunction(i+5, I^2/(J*I)))
apply(toList(-3..1), i->hilbertFunction(i, Ext^3(S^1/K3, S^{-3})))

-- What is the map defined by 4.1??
--u = 3.
betti res(S^1/K2)
R2 = S/K2
a2bar = sub(J_2, R2)
Ibar = sub(I,R2)
L2 = (ideal a2bar): Ibar
K3bar = sub(K3,R2)
gens(K3bar) % L2
compress ((gens L2)%K3bar) -- a principal ideal of S/K3 defines R2/(a2bar:Ibar)
