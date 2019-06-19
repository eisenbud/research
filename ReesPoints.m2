needsPackage "Points"
needsPackage "ReesAlgebra"
load "SymmetricPower.m2"

reesDegrees = n-> (
    m:= 2;
    while binomial(m,2)<= n do m = m+1;
    m = m-1;
    s := n-binomial(m,2);
    t := m-s-1;
I := randomPoints(2,n);
J := reesAlgebraIdeal (I, (ring I)_2);
L := (J_*/degree);
if t>= s then (
    (n,s,t, (L/(d -> {d_1-(s+t)*d_0, d_0})))
    )
    else
    (n,s,t,L/(d->reverse d))
)
st = n->(
    m:= 2;
    while binomial(m,2)<= n do m = m+1;
    m = m-1;
    s := n-binomial(m,2);
    t := m-s-1;
    (s,t))

symmetricTorsionPoints = n->(
I := randomPoints(2,n);
J := reesAlgebraIdeal (I, (ring I)_2);
J0 := symmetricAlgebraIdeal(I);
tors := (J/J0);
annihilator tors)

///
restart
load"ReesPoints.m2"
time (n,s,t,L) = reesDegrees 18
netList L

time symmetricTorsionPoints 23


param = ZZ[x,y]
listListToListMonomial = ell -> (apply(ell, i-> x^(i_0)*y^(i_1)))
listListToListMonomial ell

Ltot = apply({6,7,8}, n-> reesDegrees n)
Lpure = select(Ltot, ell ->ell_1<=ell_2)

apply(Lpure, ell -> {ell_0,ell_1,ell_2, listListToListMonomial (ell_3)})
scan(toList(31..40), n-> <<time reesDegrees n<<endl)
///


reesPoints = n->(
po := randomPoints(2,n);
(po,reesIdeal po)
)
symmetricTorsion = method()
symmetricTorsion(ZZ,ZZ) := (n,j) ->(
    P := randomPoints(2,n);
    symp :=symmPower (j,module P); -- using substitute for built-in symmetricPower!
    prune((image saturateLinear (presentation symp))/image presentation symp)
--    prune(saturate (0_symp, (ring symp)_2)
)

symmetricTorsion1 = (n,j) ->(
    P := randomPoints(2,n);
    symp :=symmPower (j,module P); -- using substitute for built-in symmetricPower!
--    prune((image saturateLinear (presentation symp))/image presentation symp)
    prune saturate(0_symp, (ring symp)_2)
)
///
restart
load"ReesPoints.m2"
kk= ZZ/101
n = 6;
j= 3;



mm = ideal vars S
I = intersect(mm^4,monomialCurveIdeal(S,{5,6,7}))
prune (saturateLinear I/I)
phi = presentation (S^1/I)

prune ((image saturateLinear phi)/image phi)

N = image saturateLinear phi
target gens N == target phi
target phi
target gens ((gens gb phi)_{0}) == target phi

n=6
j=3
symmetricTorsion (n,3)
///


symmetricTorsion2 = method()
symmetricTorsion2(ZZ,ZZ,ZZ) := (n,j,pow) ->(
    P := randomPoints(2,n);
    S := ring P;
    symp :=symmetricPower (3,module P);
    mm2 = ideal(S_0^2);
    symp' := 
    symp1 := quotient(symp, ideal(S_2), Strategy=>Linear);
    symp2 := quotient(symp1, ideal(S_2), Strategy=>Linear);
   prune symp2
)

saturateLinear = method()
saturateLinear Ideal := I ->(
    --saturates with respect to last variable
    --assuming that we're in revlex
    S := ring I;
    n := numgens S;
    var = S_(n-1); -- the last variable
    G := ideal gens gb I;
    ini := ideal leadTerm G;
    M := null;
    M':= null;
    trim sum apply(numgens ini, i -> (
	    M = ideal ini_i;
	    M' = saturate(M,S_3);
	    ideal(G_i):(M:M')
	    ))
    )
saturateLinear Matrix := phi ->(
    --returns map onto the saturation of the image of phi
    S := ring phi;
    n := numgens S;
    var = S_(n-1); -- the last variable
    G :=  gens gb phi;
    ini := leadTerm G;
    M := null;
    M':= null;
	gens sum apply(numcols ini, i -> (
	    M = image ini_{i};
	    M' = saturate(M,var);
	    (image G_{i}):(M:M')
	    ))
    )
    
statistics = method(Options =>{Kind => Rees, Verbose => false})
statistics ZZ := o-> n->(
    m:= 2;
    while binomial(m,2)<= n do m = m+1;
    m = m-1;
    s := n-binomial(m,2);
    t := m-s-1;
    po := randomPoints(2,n);
    B := betti res po;
    IRees := null;
    Isym := null;    
    I := null;

    if o.Kind == Rees then
    I = reesIdeal po

     else if o.Kind == Symmetric then
    I = symmetricAlgebraIdeal po

     else if o.Kind == Torsion then
         IRees = reesIdeal po;
         Isym = symmetricAlgebraIdeal po;
         I = prune (sub(IRees, ring Isym)/Isym);

    S = ring I;
    (R,RS) = flattenRing S;
    if o.Kind == Torsion then
     IR = coker RS presentation I else(
    IR = RS I;
    B = betti (F = res IR);
    dep = 1+max(s,t)+3 - pdim coker gens IR);
    
    if o.Kind == Rees then(
	if o.Verbose == true then
        (n, s,t,dep,B,IR_*/degree)
	  else (n, s,t,dep))
      
    else if o.Kind ==Symmetric then(
    if o.Verbose == true then(
    (n, s,t,max(numgens po, 3),dep,B, betti po))

    else
    (n, s,t,dim IR,dep))

    else if o.Kind == Torsion then
    (n,s,t,betti res I)
    )

    

///
restart
load "ReesPoints.m2"
statistics (11, Kind=>Torsion)
po = randomPoints(2,11);
IR = reesAlgebraIdeal po;
Isym = symmetricAlgebraIdeal po;
prune (sub(IR, ring Isym)/Isym)

///
end--
restart
load "ReesPoints.m2"
statistics 11
statistics (11, Kind=>Symmetric, Verbose => true)
(po,I) = reesPoints 17;
betti res po
S = ring I
(R,RS) = flattenRing S
IR = RS I;
I_*/degree
netList(I_*)
betti (F = res IR)
kk = coefficientRing ring IR
R1 = kk[W_0..W_3,X_0..X_2, Degrees =>flatten {4:{1,0},3:{0,1}}]
fl = map(R1,R,{W_0..W_3,X_0..X_2})
isHomogeneous fl IR
IR_*/degree
minimalBetti fl IR
F1 = fl F
betti fl(F)
--
for n from 23 to 24 do--21+94 seconds
time print statistics n
--for 23:
netList{{1, 7}, {1, 7}, {1, 8}, {1, 8}, {3, 19}, {3, 19}, {3, 19}, {4, 25}, {4, 25}, {4, 25}, {4, 25}, {5, 30}, {5, 30}, {5, 30}, {6, 36}, {6, 36}, {6, 36}, {6, 36}, {8, 48}, {8, 48}, {8, 48}, {8, 48}, {8, 48}}
--for 24:
netList {{1, 8}, {1, 8}, {1, 8}, {3, 20}, {3, 20}, {3, 20}, {6, 37}, {6, 37}, {6, 37}, {6, 37}, {6, 37}, {6, 37}, {6, 37}, {6, 37}, {6, 37}, {6, 37}, {6, 37}, {6, 37}, {6, 37}, {6, 37}, {6, 37}, {12, 72}}

for n from 6 to 25 do
time print statistics(n, Kind=>Symmetric, Verbose => true)

for n from 6 to 25 do
time print statistics(n, Kind=>Torsion, Verbose => true)

restart
load"ReesPoints.m2"
time netList for n from 5 to 40 list
{n, annihilator symmetricTorsion1(n,3)}

time betti res symmetricTorsion1(23,5)
time minimalBetti symmetricTorsion1(23,6)


S = ZZ/101[x_0..x_3]
P = randomPoints(2, 19)

presentation module Pfgae45    	       	       	                
symmetricPower(3,target presentation module P)
code methods symmetricPower

S = ZZ/101[x_0..x_2]
P = randomPoints(2, 19)
symp = symmPower(3, module P);
S === ring symp
saturate(symp_0, (ring symp)_2)

P3 = presentation symmPower(3, module P);
P31 = trim image saturateLinear(oo);
prune(P31/image P3)


time symmetricTorsion1(19,3)
time symmetricTorsion(19,3)

--fiber ring of 23 points:

T = ZZ/101[y_0..y_4]
F = ker map(ring I, T, gens I)
minimalBetti F


------Justin's example -- bug!
restart
loadPackage("ReesAlgebra", Reload =>true)
R = QQ[x_1..x_4]
I = ideal(x_1*x_2, x_3*x_4)
--I = ideal(x_1*x_2, x_3*x_4, x_2*x_3, x_2*x_4)
IR = reesIdeal (module I, I_0)
presentation symmetricAlgebra module I
presentation module I
reesAlgebra (module I, I_0)
code (symmetricAlgebra, Module)
mingens I
symmetricKernel mingens I
sub(IS, ring IR) + IR == IR
code methods reesAlgebra


