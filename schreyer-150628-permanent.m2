vertex = method()
vertex Ideal := I->(
    R := ring I;
    M := transpose contract(transpose vars R, gens I);
    N := syz (M, DegreeLimit =>-1);
    ideal (vars R * N)
    )
TEST///
S = ZZ/101[a..d]
I1 = ideal"a2+b2"
assert(vertex I1 == ideal"c,d")
I2 = ideal"abc"
assert(vertex I2 == ideal"d")
///
end--

restart
n=4
S2 = ZZ/2[x_(1,1)..x_(n,n)]
m= transpose genericMatrix(S2, x_(1,1),n,n)
K2 = apply(n, i-> koszul(i+1,m^{i}))
perm2= det m

S =  ZZ/101[z,x_(1,1)..x_(n,n)]
perm = sub(perm2, S)
j = trim ideal jacobian ideal perm;
betti  j
time codim j
time degree j

K = apply(K2,k-> sub(k,S))
M1 = directSum K
ones = map(target M1, source M1, (i,j) -> if j==i-1 then 1_S else 0_S)
M = map(S^(2^(n)-1), , M1+z*ones)
isHomogeneous M
perm = det M//z^(2^n-n-1)
D = det M
R = S/(ideal D)
MR = prune coker (R**M)
E = Ext^1(MR, MR);
betti prune E


    F = res (coker (R**M), LengthLimit => 5)
betti    F.dd_2
    K = ker ((transpose F.dd_2)**MR);
    betti K

ambient K == (dual F_1) ** F_0
(generators K)_{0,1}
keys K.cache
K.RawFreeModule
map(ambient K, cover K)
betti K_{0}

    (target K_{0}) == Hom(target(F.dd_2), coker (R**M))
target (K_{0})

(syz gens minors(6,M))_{0}


restart
n = 4
m = 8
kk=ZZ/101
S = kk[z, x_0..x_(m-1),y_0..y_(m-1),l_(0,0)..l_(m-1,m-1)]
row1 =  matrix{toList (x_0..x_(m-1))}
col1 =  S^{-1}**transpose matrix{toList (y_0..y_(m-1))}
L = S^{-1}**transpose genericMatrix(S,l_(0,0),m,m)
diag = diagonalMatrix toList(m:z)
zer = matrix{{0_S}}
M = (zer|row1) || (col1|(L+diag))

--coeff of z^m-1
sum(m, i->x_i*y_i)
--coeff of z^m-2

term1 = sum(m, i-> (
	x_i*y_i*(sum(m,k->(if k != i then l_(k,k) else 0_S)))))
term2 = sum(m, i->(sum(m,j->(if i !=j then
		x_i*y_j*l_(i,j) else 0_S))))
coef2 = -term1+term2
--D = det M;
--sub(contract(z^2,D), {z=>0}) == -term1 +term2

sub1 = apply(4, i->x_(i+4)=>0) | apply(4, i->y_i=>0)
f1 = map(S,S, sub1)
f1 coef2
quads = mingens f1((ideal row1)*ideal(col1))
contract (transpose quads, coef2)
(syz quads)*random(source syz quads,S^{-3})
mingens ideal transpose oo


M




restart
n=3
S2 = ZZ/2[x_(1,1)..x_(n,n)]
m= transpose genericMatrix(S2, x_(1,1),n,n)
K2 = apply(n, i-> koszul(i+1,m^{i}))

S =  ZZ/101[z,x_(1,1)..x_(n,n)]
K = apply(K2,k-> sub(k,S))
M1 = directSum K
ones = map(target M1, source M1, (i,j) -> if j==i-1 then 1_S else 0_S)
M = map(S^(2^(n)-1), , M1+z*ones)
isHomogeneous M
perm = det M//z^(2^n-n-1)
D = det M
R = S/(ideal D)
MR = prune coker (R**M)
E = Ext^1(MR, MR);
betti prune E

MM = coker M
pp = ideal perm 
betti prune(pp*MM/(pp^2*MM))
betti prune ker map(MM,MM,perm*id_MM)

ann coker M

ann coker M == ideal(z^(n-1)*perm);
annElt = (ann coker M)_0;
N = map(target M,,annElt*id_(target M)//M);
betti N
--N1 = sub(N, {z=>1})
N1 = N;
betti N1;


N1_{0..n}^{n..2^n-2};
N1_{0}^{0..n-1}
N3 = N1_{1..n}^{0..n-1};
N3-perm*id_(target N3)
K_1*K_2*K_0
N3 == map(target N3,,z^1*(perm*id_(target N3)-K_1*K_2*K_0))
N4 = N1^{0..n-1}_{4..6}
rank N4
div1 = syz transpose syz N4
N4' = transpose((transpose N4)//div1)
N4'*(transpose div1) == N4
div2 = syz transpose syz transpose N4
N4'' = N4'//div2
div2 * N4'' * (transpose div1) == N4

D1 = map(target transpose N4'',,diagonalMatrix toList (x_(2,1)..x_(2,3)))
N4''' = (transpose N4'')//D1
N4'' == (transpose N4''')*transpose D1

D2 = map(target transpose N4''',,diagonalMatrix{x_(2,3),x_(2,1),x_(2,2)})
N4'''' = (transpose N4''')//D2
transpose N4''' == D2* N4''''

N4'' == D2* N4'''' *transpose D1

N4 == div2 * D2*N4''''*(transpose D1) * (transpose div1)

P = map(target D1,,matrix apply(3, i->apply(3, j->(if ideal D1_{i} == ideal D2_{j} then 1_S else 0_S))))
D1 - P*D2*(P^-1) == 0
(P*D2*(P^-1))
D2 - (P^-1)*D1*P == 0

D1' = map(target D2,source D2,D1)
N4 == (div2*P^-1)* D1 * (P*N4'''') * D1 * transpose div1
P*N4''''
D1 * (P*N4'''') * D1
rank N4
rank div2
A = P*N4''''
det( z*id_(target A) - A)
factor oo
ker (A+id_(target A))
ker (A-2*id_(target A))
Q = S**matrix{{1,0,0},{0,1,1},{2,-1,1}}
Q*A*transpose Q
D1*(Q^-1)
(transpose Q)^-1*D1
(div2*P^-1)
transpose div1


-------
restart
n=4
S2 = ZZ/2[x_(1,1)..x_(n,n)]
m= transpose genericMatrix(S2, x_(1,1),n,n)
K2 = apply(n, i-> koszul(i+1,m^{i}))

S =  ZZ/101[z,x_(1,1)..x_(n,n)]
K = apply(K2,k-> sub(k,S))
M1 = directSum K
ones = map(target M1, source M1, (i,j) -> if j==i-1 then 1_S else 0_S)
M = M1+z*ones	
ann coker M
perm = det M//z^(2^n-n-1);
ann coker M == ideal(z^(n-1)*perm);
annElt = (ann coker M)_0;
N = map(target M,,annElt*id_(target M)//M);
betti N
--N1 = sub(N, {z=>1})
N1 = N;
betti N1;


N1_{0..n}^{n..2^n-2};
N1_{0}^{0..n-1}
N4 = N1_{1..n}^{0..n-1};
N4 == map(target N4,,z^2*(-perm*id_(target N4)-K_1*K_2*K_3*K_0))
rank N4
div1 = syz transpose syz N4
perm//transpose(syz syz div1)

--worked out to here.

syz transpose N4
N4' = transpose((transpose N4)//div1)
N4'*(transpose div1) == N4
div2 = syz transpose syz transpose N4
N4'' = N4'//div2
div2 * N4'' * (transpose div1) == N4

D1 = map(target transpose N4'',,diagonalMatrix toList (x_(2,1)..x_(2,3)))
N4''' = (transpose N4'')//D1
N4'' == (transpose N4''')*transpose D1

D2 = map(target transpose N4''',,diagonalMatrix{x_(2,3),x_(2,1),x_(2,2)})
N4'''' = (transpose N4''')//D2
transpose N4''' == D2* N4''''

N4'' == D2* N4'''' *transpose D1

N4 == div2 * D2*N4''''*(transpose D1) * (transpose div1)

P = map(target D1,,matrix apply(3, i->apply(3, j->(if ideal D1_{i} == ideal D2_{j} then 1_S else 0_S))))
D1 - P*D2*(P^-1) == 0
(P*D2*(P^-1))
D2 - (P^-1)*D1*P == 0

D1' = map(target D2,source D2,D1)
N4 == (div2*P^-1)* D1 * (P*N4'''') * D1 * transpose div1
P*N4''''
D1 * (P*N4'''') * D1
rank N4
rank div2
A = P*N4''''
det( z*id_(target A) - A)
factor oo
ker (A+id_(target A))
ker (A-2*id_(target A))
Q = S**matrix{{1,0,0},{0,1,1},{2,-1,1}}
Q*A*transpose Q
D1*(Q^-1)
(transpose Q)^-1*D1
(div2*P^-1)
transpose div1

---
restart
S = ZZ/101[x,y,z]
f = z*y^2-x^2*(x+z)
p = ideal(x+z, y)
ch = map(S,S,{x-z,y,x+z})
R = S/(ideal ch f)
p3R = saturate (((ch p)*R)^3)
sy = syz gens p3R
sub(sy, {z=>1})


----
restart
load "schreyer-150628-permanent.m2"
kk= ZZ/101
S = kk[a_(0,0)..c_(1,1)]
A =transpose genericMatrix(S,a_(0,0), 2,2)
eA = ideal A
B = transpose genericMatrix(S,b_(0,0), 2,2)
eB = ideal B
I = trim ideal(A*B+B*A)
vars S
betti res I
netList first entries gens I
Iterms = trim ideal flatten ((first entries gens I)/terms)
netList (dJ=decompose (J=(I:eA*eB)))
netList first entries gens J
betti res J
betti res I
apply(dJ, j->betti res j)
transpose gens dJ_0


vertex(dJ_1)
dJ_1
betti res dJ_1
dJ_1_2

P1 = matrix{{0, a_(1,0), -a_(0,1), 2*a_(1,1)},
    {0,0, b_(1,1), b_(1,0)},
    {0,0,0, b_(0,1)},
    {0,0,0,0}}
P = P1-transpose P1
c_(0,0)
C = genericMatrix(S, c_(0,0),1,4)
C0 = matrix{{c_(
relns = trim ideal (C*P)
endo = vars S % (ideal (trace A, trace B)+relns)
A1 = sub(A, endo)
B1 = sub(B, endo)
assert(A1*B1==-B1*A1)
