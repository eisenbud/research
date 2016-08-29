restart
kk= ZZ/101
R = kk[x,y,a,b,c,d]
i = 10
I = ideal(x^3,y^3,x^2*a^i+x*y*b^i+y^2*(a*c^(i-1)+b*d^(i-1)));
load "eisenbudgoto.m2"
P = reesPrime I;
degree P
betti res P
ring P
Q = polarHomogenize P;
S = ring Q
--betti res Q

n = 5
T = kk[u_1..u_n]
f = map(T,S,vars T |random(T^1,T^{12-n:-1}))
time QT = f Q;
QTs = saturate QT;
QTs = QT:ideal(u_1);
betti QT
time QTs = QTs:ideal(u_1^2);
betti QTs
end--
restart
load "160827-McCullough.m2"

restart
kk = ZZ/101
S = kk[a,b,c,f,g,h, Degrees => {3:5,3:1}]
R = S/ideal"af+bg+ch"
I = ideal"f,g,h"
threeDiagonal = n ->(
matrix apply(n, i-> apply(n+2, j->(
	    if i<=j and j<=i+2 then I_(j-i) else 0_(ring I)))))
scan (4, n-> print betti res(coker threeDiagonal (n+1), LengthLimit =>2))


M2 = threeDiagonal 2
syz M2
P2 = h*matrix"a,b,c,0" + matrix"0,0,0,-bf-cg"
P2' = f*matrix"0,a,b,c"+ matrix"-ag-bh,0,0,0"

assert(M2*transpose P2==0)
assert(M2*transpose P2'==0)

---
M3 = threeDiagonal 3

M3*transpose Q
P = R^{-12}**transpose (syz M3)_{8} -- unique syzygy of highest degree
Q = a*(P2'|matrix"0")-c*(matrix"0"|P2) 
P-Q-- Q is surprisingly close to P

Q1 = matrix"a,b,c,0,0"
Q2 = matrix"0,0,a,b,c"
Q3 = matrix"0,0,0,h,-g"
Q4 = matrix"g,-f,0,0,0"
Q5 = matrix"h,0,-f,0,0"
Q6 = matrix"0,0,a,0,-c"
P'=map(R^1,, 
      -b*h*Q1 + 
      b*f*Q2 - 
      c^2*Q3 -
      a^2*Q4 -
      a*b*Q5 -
      b*f*Q6)
assert(P==P')
---

