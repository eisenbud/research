needsPackage "MCMApproximations"
envelopingAlgebra = method()
envelopingAlgebra(RingMap, Ring) := (rho,R) -> (
    --Here rho: A --> S is an inclusion of standard graded polynomial rings
    --and R = S/IR is a factor ring
    -- such that A--> R
    --is finite. The script returns the enveloping algebra 
    --
    --Re := R **_A R,
    --the map unit: map A --> Re,
    --the map aug: Re --> R, 
    --such that aug*unit is the composition of rho with the projection, A-->S-->R
    --and the diagonal ideal,
    --D = ker Aug.
    --
    S := target rho;
    k := coefficientRing S;
    A := source rho;
    A' = rho vars A;
--now form a matrix of vars of S complementary to A' = rho vars A:
--so that the entries of A'|C are a basis of the span of vars S
    C :=  map(S^1, S^{numgens S - numgens A :-1}, 
        gens trim ideal (vars S%ideal(A'))
	);
--assert(A'|C == rearrangeS vars S);
    iso := sub(vars S//(A'|C),k);
    --the following map moves the A variables to be the first numgens A vars of S
    rearrangeS := map(S,S,(vars S)*iso^(-1));
--    rearrangeR := map(R,R,(vars R)*iso^(-1));
    --and the following undoes the rearrangement, but at the level of R
    goBackR := map(R,R,(vars R)*iso);
--    goBackS := map(S,S,(vars S)*iso);    

    IR := ideal presentation R; -- ideal of S
    I' := rearrangeS IR;

--make an algebra that will map onto the enveloping algebra
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
--  make a ring map fixing the A vars and interchanging the other groups    
    exchange := map(S2,S2,Avars|newvars2|newvars); 

--make the enveloping algebra
    insS := map(S2,S,(vars S2)_{0..numgens S -1}); -- inclusion of S in S2 as first vars
    I'' := insS I';
    IRe := trim(I'' + exchange I'');
    Re := S2/(IRe);
--and the associated maps and ideals
    unit := map(Re,S2)*insS*rearrangeS*rho;
    aug := goBackR * map(R,Re,(vars R)|(vars R)_{(numgens A)..(numgens R-1)});
    D := sub(diagS2, Re);

    (Re, unit, aug, D)
    )
env = envelopingAlgebra
TEST///
restart
load "161108-iyengar.m2"
kk= ZZ/101
A = kk[x]
S = kk[x,y]
R = S/ideal(x^2,y^2)
rho = map(S,A)
(Re,unit,aug,D) = env(rho, R)
assert (dim Re == 0)
map(R,S)*rho === (aug*unit)

kk = ZZ/101
A = kk[A,B]
S = kk[u,v,x,y]
rho = map(S,A,{v,x})
R = S/ideal(x^2,y^2)
(Re,unit,aug,D) = env(rho, R)
assert (dim Re == 3)
assert(map(R,S)*rho === (aug*unit))
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

----
restart
kk = ZZ/101
A = kk[A,B]
S = kk[u,v,x,y]
rho = map(S,A,random(S^1, S^{2:-1}))
A' = rho vars A
C = map(S^1, S^{numgens S - numgens A :-1}, 
	transpose ((vars S)// A'*transpose vars S)
	);
vars S * (((A'|C)//(vars S))) == A'|C

    S2 = kk[a_1..a_(numgens A), 
	   X_1..X_(numgens S - numgens A),
	   Y_1..Y_(numgens S - numgens A)]
    Avars = matrix{{a_1..a_(numgens A)}};
    newvars = matrix{{X_1..X_(numgens S - numgens A)}};
    newvars2 = matrix{{Y_1..Y_(numgens S - numgens A)}};
    diagS2 = ideal(newvars - newvars2);
    exchange = map(S2,S2,Avars|newvars2|newvars);
    vars S * ((A'|C)//(vars S))
    
    


    ins = map(S2,S,
insS*rho

    A' = rho vars A;
    C =  map(S^1, S^{numgens S - numgens A :-1}, 
	vars S*transpose (vars S // A')
	);
    map(S,S,A'|C)
    det (vars S//(A'|C))
    

A'|C

vars S // A'

restart
kk= ZZ/101
A = kk[x]
S = kk[x,y]
R = S/ideal(x^2,y^2)
rho = map(S,A)


A = kk[A,B]
S = kk[u,v,x,y]
rho = map(S,A,random(S^1, S^{2:-1}))

A' = rho vars A
C =  map(S^1, S^{numgens S - numgens A :-1}, 
   gens trim ideal (vars S%ideal(A'))
	);
A'|C


    rearrangeS = map(S,S,(vars S)*iso)
    matrix  map(S,S,(vars S)*iso)
    rearrangeR = map(R,R,A'|C);
    iso = sub((vars S)//(A'|C),kk)
     A'|C == map(S^1, source vars S, (vars S)*iso)
     
