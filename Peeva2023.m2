needsPackage "RandomIdeals"
needsPackage "CompleteIntersectionResolutions"

minors1 = method()
minors1 Module := M -> minors1 res M
minors1 ChainComplex  := List =>  F -> (
    m := min F;
    if F.dd_(m+1) !=0 then m = m+1 else m = m+2;
    for i from m to max F list trim ideal F.dd_i
    )
minors1 (ZZ, Module) := (k,M) ->(
    --back-and-forth resolution over an artin Gorenstein ring
    F := res(M, LengthLimit => k);
    F = res (coker (dual (F.dd_(length F))), LengthLimit => 2*k);
    minors1 res (coker (dual (F.dd_(length F))), LengthLimit => 2*k)
    )

conjecture = (M) ->(
R := ring M;
S := ambient R;
RS := map(R,S);
F := res(prune M, LengthLimit => numgens R +1);
print betti F;
print netList(L=  minors1 F);
print trim sum L;
MS := for i from 1 to numgens R+1 list
   pushForward(RS, coker F.dd_i);
MMS := directSum MS;
print netList (LS := minors1 MMS);
print trim sum LS)


end--

restart
load "Peeva2023.m2"
kk = ZZ/101
S = kk[a,b,c,d,e]
I = ideal(a*b*c)+ ideal for i from 0 to numgens S-1 list S_i^5
R = S/I
M = module ideal"ab+cd, bc2d, a3"
conjecture M

RS = map(R,S)
MS = prune pushForward(RS, M)
FS = res(MS)
netList minors1 FS

R = S/ideal(a^5, b^5)

M = module randomBinomialIdeal({2,3},R)
conjecture M
F = res(M, LengthLimit => 5)
netList minors1 F
M1 = coker F.dd_4;
M1S = prune pushForward(RS, M1);
F1S = res(M1S)
netList minors1 F1S
--betti res evenExtModule M
--betti res oddExtModule M
min F
netList minors1 F
kkk = coker vars R


use R
M = module ideal "ab"
conjecture M
M = module ideal"ab, bc2d, a2d"
conjecture M
M = module randomBinomialIdeal({2,2}, R)
conjecture M
M = coker random(R^2, R^{-1})
netList minors1(4, M)
use R
--betti res evenExtModule M
--betti res oddExtModule  M



--trying to understand the M2 presentation of Ext
S = kk[x,y]
I = ideal(x^3,y^3)
R = S/I
M = ideal x^3
kkk = coker vars R
ex = Ext(kkk,kkk)
E = ring ex
E_2
ex' = prune coker sub(presentation ex, {E_2=>0,E_3 =>0})

betti(ex', Weights => {-1,0})
E = ring ex
T = kk[t_1..t_(numgens I)]
use E
sub(presentation ex, x =>0)
degrees oo
prune(ex/(E_1*ex))
phi = map(T, E, {t_1..t_(numgens I),numgens R: 0})


--Gasharov-Peeva last example:
restart
load "Peeva2023.m2"
n = 4
x = symbol x;y=symbol y;
S = ZZ/32003[x_1..x_3,y_1..y_n]
I1 = ideal(x_1^2,x_2^2, x_3^2) + ideal(x_1*y_1+x_2*y_n)+ ideal for i from 2 to n list  x_1*y_(i)+x_2*y_(i-1)
I2 = ideal (x_2*x_3-y_1^2)+ ideal for i from 2 to (1 + n//2) list x_2*x_3-y_i*y_(n+2-i)
I3 = ideal for i from 1 to ((1 + n)//2) list x_1*x_3+y_i*y_(n+1-i)
I4 =  ideal(x_1^2,x_2^2, x_3^2) + ideal for i from 1 to n list x_3*y_i
L5 = flatten for i from 1 to n list 
       for j from i to n list (
       if i+j != n+1 and i+j != n+2 and j!= 1 then y_i*y_j)
I5 = ideal select(L5, x -> x =!= null)
I = trim(I1+I2+I3+I4+I5)


R = S/I
RS = map(R,S)
use R
M = coker matrix{{x_1,y_2},{0_R,x_2}}
F = res M
MMS = directSum for i from 1 to 4 list 
        prune pushForward(RS, coker F.dd_i)
FS = res(MMS)
netList minors1 FS

F = res(M, LengthLimit => 6)
netList minors1 F
M1 = coker F.dd_4;
M1S = prune pushForward(RS, M1);
F1S = res(M1S)
netList minors1 F1S

conjecture(R,M)

