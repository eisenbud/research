
--

restart
kk = ZZ/101
S = kk[a,b,x,A,B,C,X,r,s,t, u, w]
m1 = matrix"
A,X;
0,B"
m2 = matrix"
s,a,x;
t,r,b"
m3 = transpose m2
eqn = ideal(m1*m2)+ideal(m2*m3)
R = S/eqn
--betti res coker sub(m1,R) -- doesn't return, but with LengthLimit=>10 does in 12.4 sec
time betti (F = res (coker sub(m1,R),LengthLimit => 6))
F.dd_3
F.dd_2


--- Example from Gasharov-Peeva
restart
kk = ZZ/101
S = kk[x_1..x_4]
m = matrix
m1 = matrix{{
x_1,x_3+x_4},
{0,x_2}}
m2 = matrix{{
x_1,3*x_3+x_4},
{0,x_2}}
m3 = matrix{{
x_1,9*x_3+x_4},
{0,x_2}}

eqn = trim (ideal (m1*m2)+ideal(m2*m3) + ideal(x_3*x_4))
gens (eqn:(ideal gens S))%eqn

R = S/eqn
betti (F =  res coker sub(m1,R))
F.dd_2
dim R
betti res (S^1/eqn)
x,as+tb;
0,y"
m1 = map(S^{0,-1}, S^{ -1,-2},matrix"
x,a2s+tb2;
0,y2")


---Gasharov-Peeva 2
restart
kk = ZZ/101
n = 3
S = kk[x_1,x_2,y_0..y_(n-1)]
mm = apply(n, i-> matrix{{x_1,y_(i%n)},{0,x_2}})
eqn = trim sum apply(n, i->ideal(mm_i*mm_((i+1)%n)))
eqn' = (ideal (vars S)_{2..n+1})^2
R = S/(eqn+eqn')
betti (F =  res(coker sub(mm_0,R), LengthLimit => n+2))
F.dd_3
---

---
restart
kk = ZZ/101
n = 3
(p,q,r) = (2,2,3)
S = kk[x_1,x_2,y_0..y_(n-1),s,t]
mm = apply(n, i-> matrix{{x_1,y_(i%n)},{0,x_2}})
use S
eqn = trim sum apply(n, i->ideal(mm_i*mm_((i+1)%n)))
eqn' = (ideal (vars S)_{2..n+1})^2
eqn'' = ideal( mm_0*matrix"s;t")
eqn''' = ideal(s)*ideal((vars S)_{2..n+1})+ideal(y_2*t,s*t,s^2)

use S
R = S/(eqn+eqn'+eqn''+eqn''')
betti (F =  res(coker sub(mm_0,R), LengthLimit => n+2))
F.dd_1
F.dd_2
F.dd_3




restart
kk = ZZ/101
S= kk[a,b,x,y,z,s,t, u,w]
m1 = matrix"
a,x;
0,b"
m2 = matrix"
s,a,y;
t,0,b"
m3 = matrix"
u,w;
a,z;
0,b"

eqn = trim (ideal (m1*m2)+ideal(m2*m3))


R = S/eqn
betti (F =  res (coker sub(m1,R), LengthLimit =>4))
F.dd_2
extra = (F.dd_2)_{3..6}
I1 = ideal extra
R1 = R/I1
betti (F =  res (coker sub(m1,R1), LengthLimit =>4))
F.dd_2

---
--pos integral solutions of p^3+r^3+q^3-3pqr = 0
restart
S = QQ[p,q,r]
f = p^3+q^3+r^3-3*p*q*r
f(1,2,3)
scan(30, i-> apply(30, j-> apply(300, k-> (
		if sub(f, {p=>i,q=>j,r=>k})== 0 then
  print(i,j,k)))))

---
restart
kk = ZZ/101
S = kk[x,y,z]
needsPackage "LexIdeals"
I = lexIdeal(S,{1,3,3,3,3,3,2})
R=S/I
m = matrix"x,y;
0,z"
betti res coker m

use S
J = minors(2,matrix"x,y,z;y,z,x")
R = S/(J + ideal (x^6+y^6+z^6))
m = matrix"x,y;
0,z"
betti res (coker m, LengthLimit =>10)
betti res( coker matrix"x,y;
y,x", LengthLimit =>10)

betti res coker matrix"x,y,z;y,z,x"


----
restart

kk = ZZ/101
(p,q,r) = (2,2,3)
n = 6
S =kk[x_(0,0)..x_(p-1,q-1),
    y_(0,0)..y_(q-1,r-1),
    z_(0,0)..z_(r-1,p-1),
    a_0..a_(n-1)]
m1 = genericMatrix(S,x_(0,0),p,q)
m2 = genericMatrix(S,y_(0,0),q,r)
m3 = genericMatrix(S,z_(0,0),r,p)
eqn = ideal(m1*m2)+ideal(m2*m3)+ideal(m3*m1)
R = S/eqn
apply(8, i->hilbertFunction(i,R^1))
betti (F = res(coker sub(m1,R), DegreeLimit =>3, LengthLimit =>3))
q = (F.dd_2)_{3..17}
l = (F.dd_2)_{0..2}
l' = sum apply (n, i-> a_i*random(R^3,R^15))

I1 = ideal(q -l*l');
--I1 = ideal((F.dd_2)_{3..17})
R2 = R/I1
betti (F = res(coker sub(m1,R2), DegreeLimit =>3, LengthLimit =>2))

---

needsPackage "LexIdeals"