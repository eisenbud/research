///
restart
load "deformation-of-omega.m2"
kk=ZZ/101
S=kk[x]
g=matrix"x5"
R=S/ideal g
H=Hom(ideal g, S^1/ideal g)
BH=basis(H)
h1=BH_{1};
h2 = homomorphism h1
testDefOfDifferentials(g,h2)
L=for i from 0 to rank source BH - 1 list (
h=homomorphism BH_{i};
testDefOfDifferentials(g,h))
(L/toHom)/representVector


--
restart
load "deformation-of-omega.m2"
kk=ZZ/101
kk=QQ
S=kk[x,y]
g=matrix"x2,xy,y2"
h=map(S^1/ideal g, module ideal g, {{2*x,y,0}})
--the following should give 0
testDefOfDifferentials(g,h)

H=Hom(ideal g, S^1/ideal g)
BH=basis(H)

h1=BH_{0};
h2 = homomorphism h1
testDefOfDifferentials(g,h2)

L=for i from 0 to rank source BH - 1 list (
h=homomorphism BH_{i};
testDefOfDifferentials(g,h))
(L/toHom)/representVector
netList L
target L_0

f = (g,h) -> toHom testDefOfDifferentials(g,homomorphism h)
mat = representVector (f (g,H_{0}));
for i from 1 to rank source BH  -1 do(
     mat = mat | representVector (f(g,BH_{i})));
mat
K=syz mat
KH=BH*K
homomorphism KH_{0}
--
{* 
restart
load "deformation-of-omega.m2"
kk=ZZ/101
kk=QQ
S=kk[x,y]
g=matrix"x2,xy,y2"

--There's a different "report" function later
report= g -> (
     f := (g,h) -> toHom testDefOfDifferentials(g,homomorphism h);
     BH = basis Hom(ideal g, S^1/ideal g);
     mat = representVector (f (g,BH_{0}));
     for i from 1 to rank source BH  -1 do(
     	  mat = mat | representVector (f(g,BH_{i})));
     K=syz mat;
     KH=BH*K;
     for i from 0 to rank source KH -1 list homomorphism KH_{i})

netList report g     
netList report matrix"x3,xy,y3"     
netList report matrix"x5,y"
*}     
--
restart
load "deformation-of-omega.m2"
kk=ZZ/101
S=kk[x,y]
g=matrix"x2,xy,y2"
R=S/ideal g
H=basis Hom(ideal g, S^1/ideal g)

homomorphism H_{0}
testDefOfDifferentials(g,homomorphism H_{0})

basis coker(R**jacobian g)

f = (g,h) -> toHom testDefOfDifferentials(g,homomorphism h)
mat = representVector (f (g,H_{0}));
mat
for i from 1 to rank source H  -1 do(
     mat = mat | representVector (f(g,H_{i})));
mat
kernel mat

--
restart
load "deformation-of-omega.m2"
kk=ZZ/101
S=kk[x]
g=matrix"x5"
R=S/ideal g
H=basis Hom(ideal g, S^1/ideal g)

f = (g,h) -> toHom testDefOfDifferentials(g,homomorphism h)

mat = representVector (f (g,H_{0}));
for i from 1 to rank source H -1 do(
     mat = mat | representVector (f(g,H_{i})));
kernel mat

///
///
--Something's wrong with the following: I don't think td should be
--homogeneous!
restart
load "deformation-of-omega.m2"
kk=ZZ/101
S=kk[x]
g=matrix"x5"
R=S/ideal g
H=Hom(ideal g, S^1/ideal g)
BH=basis(H)
td=testDefOfDifferentials(g,gens image homomorphism BH_{0})
 betti td
isHomogeneous td -- oops! -- this should NOT be true, I think.
///





///

restart
load "deformation-of-omega.m2"
kk=ZZ/101
S = kk[x]
M=S^1
N=S^{-1}/x^5
f=map(N,M,{{x}})
representVector(f)

--
restart
load "deformation-of-omega.m2"
kk=ZZ/101
R1=kk[x,y]
S = kk[x]
R= S[y]
M=R^{{0,0},{0,1}}/(x+y^2, y^4)
M1 = R1^2
f=map(M,R^1,{{1},{0}})
representVector(f)

B=pushToField(M,5)
target B

phi = map(M,M,{{x,0},{0,y}})
pushToField(phi)
f = p->phi*p
--representMatrix(f, M, M)

basis M -- Note that this does not give a vspc basis!!
        -- it's a set of gens over S.
viewHelp basis


///
///
restart
load "deformation-of-omega.m2"
S= kk[x,y]
M = S^1/x^5
N = (S^1/x^4) ++ (S^1/(x^2*y))
f=map(N,M,{{x^2},{x*y^2}})
g=toHom f
f1=homomorphism g
f1==f
g==toHom f1
viewHelp adjoint
--the doc page is WRONG. headline should be adjoint(f,F,G), NOT adjoint(f,G,H).
///
///
restart
load "deformation-of-omega.m2"
kk=ZZ/101
kk=QQ
S=kk[x,y]
g=matrix"x2,xy,y2"
T=trivialDefs g
netList T
///

///
restart
load "deformation-of-omega.m2"
kk=ZZ/101
kk=QQ
S=kk[x,y]
g=matrix"x2,xy,y2"
T=OmegaFlatDefs g
netList T
TM=OmegaFlatDefsModule  g
degree TM
///
