newPackage(
	"EnvelopingAlgebras",
    	Version => "0.1", 
    	Date => "November 10, 2016",
    	Authors => {{Name => "David Eisenbud", 
		  Email => "de@msri.org", 
		  HomePage => "http://www.msri.org/~de"}},
    	Headline => "Enveloping Algebra of a Noether Normalization Map",
    	DebuggingMode => true
    	)

export {
    "envelopingAlgebra",
     "env"
	}

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
    A' := rho vars A;
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
env = method()
env(RingMap, Ring) := (rho,R) -> envelopingAlgebra(rho, R)

beginDocumentation()

doc ///
Key
  EnvelopingAlgebras
Headline
  Enveloping Algebra with respect to a linear Noether Normalization
Description
  Text
   Given a finite morphism of degree 0 from a standard graded polynomial ring A
   to a ring R, the enveloping algebra is $R^e:=R\otimes_A R$, with associated maps
   $unit: A \to R^e$ and $aug: R^e \to R$.
///

doc ///
Key
 envelopingAlgebra
 (envelopingAlgebra, RingMap, Ring)
Headline
 compute the enveloping algebra and associated maps and ideals
Usage
 (Re,unit,aug,D) =  envelopingAlgebra(rho, R)
Inputs
 rho:RingMap
  degree 0 inclusion of standard graded polynomial rings A --> S
 R:Ring
  ring of the form S/I, finite over A
Outputs
 Re:Ring
  the enveloping algebra $R\otimes_A R$
 unit:RingMap
  the natural map $A\to Re$
 aug:RingMap
  the natural map $Re \to R$
 D:Ideal
  ideal of Re, kernel of aug
Description
  Text
   Given a finite morphism of degree 0 from a standard graded polynomial ring A
   to a ring R, the enveloping algebra is $R^e:=R\otimes_A R$, with associated maps
   $unit: A \to R^e$ and $aug: R^e \to R$.
   
   The following shows how to use this to test the hypothesis that the universal annihilator
   of the higher Ext modules is given by pushing forward the 
   associated graded ring of R^e with respect to the augmentation ideal, in a very special
   case. For k[x]/x^n, the universal annihilator is x^m where m is the floor of n/2.
  Example
   kk= ZZ/101
   n = 7
   S = kk[x]
   rho = map(S,kk)
   R = S/ideal(x^n)
   (Re,unit,aug,D) = env(map(S,kk), R)
   --test components of the associated graded ring to see whether they
   --give the righ annihilator of Ext^(dim +1)(-,-)
   netList apply(2*n, m'->(
	   m = m'+1;
           M = coker aug presentation (module (D^m)/module(D^(m+1)));
           oM = image((res M).dd_1);	   
           ann Ext^1(M,oM)
               ))
Caveat
  rho must be linear
///
doc  ///
Key
 env
 (env, RingMap, Ring)
Headline
 synonym for envelopingAlgebra
Usage
 (Re,unit,aug,D) =  env(rho, R)
Inputs
 rho:RingMap
  degree 0 inclusion of standard graded polynomial rings A --> S
 R:Ring
  ring of the form S/I, finite over A
Outputs
 Re:Ring
  the enveloping algebra $R\otimes_A R$
 unit:RingMap
  the natural map $A\to Re$
 aug:RingMap
  the natural map $Re \to R$
 D:Ideal
  ideal of Re, kernel of aug
Description
 Text
  synonym for envelopingAlgebra
SeeAlso
 envelopingAlgebra
 ///

TEST///
restart

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

end--
restart
uninstallPackage "EnvelopingAlgebras"
installPackage "EnvelopingAlgebras"
check  "EnvelopingAlgebras"
viewHelp EnvelopingAlgebras

kk= ZZ/101
n = 7
S = kk[x]
rho = map(S,kk)
R = S/ideal(x^n)
(Re,unit,aug,D) = env(map(S,kk), R)

--test components of the associated graded ring to see whether they
--give the righ annihilator of Ext^(dim +1)(-,-)
netList apply(2*n, m'->
    (m = m'+1;
     M = coker aug presentation (module (D^m)/module(D^(m+1)));
     --M = R**(module(D^m)/module(D^(m+1)));
     oM = prune syzygyModule(1,M);
     use R;
     ann Ext^1(M,oM)
     )
)

k = ZZ/101
A = k[x]
S = k[x,y,z]
R = S/ideal(x*y^2 - z^3)
rho = map(S,A)

(Re,unit,aug,D) = env(map(S,kk), R)

--test components of the associated graded ring to see whether they
--give the righ annihilator of Ext^(dim +1)(-,-). In this case, these
--modules all have finite projective dimension!!
needsPackage "MCMApproximations"
scan(10, m'->
    (m = m'+1;
     M = coker aug presentation (module (D^m)/module(D^(m+1)));
     --M = R**(module(D^m)/module(D^(m+1)));
     oM = prune syzygyModule(1,M);
     use R;
     print betti res (M, LengthLimit => 4);
     print ann Ext^3(M,oM)
     )
)
