needsPackage "MCMApproximations"
envelopingAlgebra = method()
envelopingAlgebra(RingMap, Ring) := (rho,R) -> (
    --Here rho: A --> S is a map of polynomial rings
    --over a field k whose variables have degree 1,
    --and R = S/IR is a factor ring
    -- such that A--> R
    --is finite. The script returns the ring 
    --Re := R **_A R,  the map Re --> R, and the kernel D 
    --of this map. We assume that the generators of A
    --are the first elements of vars S, and that all is homogeneous.
    --Note that Re is bihomogeneous, with vars of degree
    S := target rho;
    A := source rho;
    k := coefficientRing S;
    IR := ideal presentation R; -- ideal of S
    X := symbol X;
    Y := symbol Y;
    a := symbol a;
    S2 := k[a_1..a_(numgens A), 
	   X_1..X_(numgens S - numgens A),
	   Y_1..Y_(numgens S - numgens A)];
    Avars := matrix{{a_1..a_(numgens A)}};
    newvars := matrix{{X_1..X_(numgens S - numgens A)}};
    newvars2 := matrix{{Y_1..Y_(numgens S - numgens A)}};
    diagS2 := ideal(newvars - newvars2);
    exchange := map(S2,S2,Avars|newvars2|newvars);
    ins := map(S2, S, Avars|newvars);
    I := ins IR;
    IRe := trim(I + exchange I);
    Re := S2/(IRe);
--    error();
    aug := map(R,Re,(vars R)|(vars R)_{(numgens A)..(numgens R-1)});
    D := sub(diagS2, Re);
    (Re,aug,D)
    )
env = envelopingAlgebra
///
restart
load "161108-iyengar.m2"
kk= ZZ/101
A = kk[x]
S = kk[x,y]
R = S/ideal(x^2,y^2)
rho = map(S,A)
(Re,aug,D) = env(rho, R)
presentation Re

A = kk
S = kk[x,y]
R = S/ideal(x^2,y^2)
rho = map(S,A)

(Re,aug,D) = env(rho, R)
presentation Re
///

end
restart
load "161108-iyengar.m2"


kk= ZZ/101
n = 7
S = kk[x]
rho = map(S,kk)
R = S/ideal(x^n)
(Re,aug,D) = env(map(S,kk), R)

netList apply(2*n, m'->
    (m = m'+1;
     M = coker aug presentation (module (D^m)/module(D^(m+1)));
     --M = R**(module(D^m)/module(D^(m+1)));
     oM = prune syzygyModule(1,M);
     use R;
     ann Ext^1(M,oM)
     )
)

restart
load "161108-iyengar.m2"
n=7
kk= ZZ/101
S = kk[x]
R = kk[x]/ideal(x^n)
S2 = kk[x,y]
Re = S2/ideal(x^n,y^n)
D = ideal(x-y)
R = Re/D
aug = map(R,Re, matrix{{x,x}})

netList apply(2*n, m'->(m = m'+1;
--M = R**(module (D^m)/module(D^(m+1)));
M = coker aug presentation (module (D^m)/module(D^(m+1)));
oM = prune syzygyModule(1,M);
use R;
ann Ext^1(M,oM)))


(Re,aug,D) = env(map(,kk), R)
