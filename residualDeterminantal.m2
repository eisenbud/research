{*
For generic determinantal ideals, 
Set:
q = n-p
s = p*q
r = p*q+1-p-q

If i>= reduction number (q-p-1 if p=2; in general) then I^i/JI^(i-1) \cong \omega_{R/K}. It is CM with
linear resolution, and self-dual.

for i>=r, and J generated by exactly s general elements it seems that I^i/JI^(i-1) is CM of codim s
and all isomorphic to omega_{R/K}, independent of i.

But in a MUCH wider range of cases I\subset S, it seems that if we set
ell = analyt spread I
r = reduction number I
K = (J:I) = (ell-1)-residual intersection, 
Ibar = I*(S^1/K)

-- (a) M := I^r/J*I^(-1) or M := Ibar^r is MCM of codim ell-1;
-- (b) M \cong I^(r+j)/J*I^(r+j-1) or Ibar^(r+j) for j>=0
-- (c) M is omega_{R/K} - self-dual. (sometimesthis isomorphism seems strange and/or inhomogeneous)
-- (d) M \cong Hom(M,M) (sometimes this isomorphism seems strange and/or inhomogeneous)
In some cases also:
-- (e) M \cong omega_{R/K}
*}


load "SymmetricPower.m2"
needsPackage "ReesAlgebra"
needsPackage "RandomIdeals"

--programs to extract the list of total betti numbers from a BettiTally
totalBetti = method()
totalBetti(ZZ,BettiTally) := (j,B) ->(
     Bj := select(keys B, k->k_0==j);
    sum(Bj, k->B#k))
totalBetti(ZZ,Module) := (j,M) -> (
    totalBetti(j, minimalBetti M))
totalBetti BettiTally := B->(
    len := max apply(keys B, k->k_0);
    apply(len+1, j -> totalBetti(j,B)))
totalBetti Module := M ->(
    totalBetti minimalBetti M)
totalBetti Ideal := I -> totalBetti minimalBetti I
totalBetti (ZZ,Ideal) := (j,I) -> totalBetti (j, minimalBetti I)

--kth power of p x p minors of generic p x n matrix (over a new ring)
detPower = {p,n,k} ->(
R := ZZ/101[x_(0,0)..x_(p-1,n-1)];
m := transpose genericMatrix(R, x_(0,0),n,p);
I := minors(p,m);
trim (I^k)
)

fastExt = method()
fastExt(ZZ,Ideal) := (i,I) -> (
        --returns Ext^i_R(I , R) = Ext^{i+1}(R/I,R).
    --for some reason the fast algorithm sometimes balks when applied to "module I"
    F := res(I, FastNonminimal=>true, LengthLimit => i+1);
    (kernel transpose F.dd_(i+1))/image transpose F.dd_i)

fastExt(ZZ,Module) := (i,M) ->(
    --let R = ring I
    --returns Ext^i_R(M , R)
    --should we minimize F.dd_(i+1)) and F.dd_(i) first?
    F := res(M, LengthLimit => i+1, FastNonminimal =>true);
   prune( (kernel transpose F.dd_(i+1))/image transpose F.dd_i)
    )
///

///

fastExt(ZZ,Module, Module) := (i,M,N) ->(
    --let R = ring I
    --returns Ext^i_R(M , R)
    --should we minimize F.dd_(i+1)) and F.dd_(i) first?
    F := res(M, LengthLimit => i+1, FastNonminimal =>true);
    prune((kernel (N**transpose F.dd_(i+1)))/image (N**transpose F.dd_i))
    )
///
restart
load "residualDeterminantal.m2"
(p,n) = (2,4)
q = n-p
s = p*q
r = p*q+1-p-q
ell = s+1

I = detPower(p,n,1);
(sI,ell,r) = specialFiberInfo(I,I_0)

time (K,M) = conj I;
minimalBetti M -- CM codim 

time M' = prune Ext^4(M,(ring M)^1)
time M'' = prune fastExt(4, M)

isHomogeneousIso(M,M')
isHomogeneousIso(M,M'')
///


rand = (I,s,d) ->
    --s elements of degree d chosen at random from I
    --need a version that uses *all* the generators, works with hom, etc
    ideal ((gens I)*random(source gens I, (ring I)^{s:-d}))


redNumber = sI ->(
    --needs a ring whose generators have degree 1
    param := rand(ideal vars ring sI, dim sI,1);
    N := (ring sI)^1/(sI+param);
    assert(dim N == 0);
    r':= 0;
    while hilbertFunction(r',N)!=0  do r' = r'+1;
    r'-1
    )

specialFiberInfo = method()
specialFiberInfo(Ideal, RingElement) := (I,a) ->(
    --a \in I\subset S, a a nzd.
    --returns (sI,ell,r), the special fiber ideal, analytic spread, reduction number
    --Note that though the generators of specialFiberIdeal(I,a) have double degrees
    --as produced by the current Rees Algebra package, the ideal is homoogeneous for
    --a single grading, with vars of degree 1.
    J := trim I;
    sJ1 := specialFiberIdeal(I,a);
    R1 := ring sJ1;
    kk := ultimate(coefficientRing, R1);
    x := symbol x;
    R := kk[x_0..x_(numgens R1 - 1)];
    sJ := trim  (map(R,R1, gens R)) sJ1;
    ell := dim sJ;
    r := redNumber sJ;
    (sJ,ell,r)
     )
specialFiberInfo Ideal := I -> specialFiberInfo(I,I_0)

///
restart
load "residualDeterminantal.m2"
(p,n) = (2,6)
q = n-p
s = p*q
r = p*q+1-p-q
ell = s+1

I = detPower(p,n,1);
time (sI,ell,r) = specialFiberInfo(I,I_0)
///

conj = I ->(
    --sets up the modules to test the conjecture.
    --ell = analyt spread I; r = reduction number I.
    --returns (K,M), where K = (J:I) an ell-1 residual intersection and
    -- M = I^r/JI^(r-1).
    --if I is equigenerated then the result is homogeneous; otherwise NOT
    d := degree(I_0);
    (sI,ell,r) := specialFiberInfo(I,I_0);
     <<(ell,r)<<endl;flush;
    --J := rand(I,ell-1,d); -- is is only ok if I is equi-generated
    kk := ultimate(coefficientRing, ring I);
    choose1 = I -> sum(I_*, i-> random(kk)*i);
    J = ideal apply(ell-1, i->choose1 I);
    (J:I,prune((module I^r)/module(J*I^(r-1))))
    )

conj' = I ->(
    --sets up the modules to test the conjecture.
    --ell = analyt spread I; r = reduction number I.
    --returns (K,M), where K = (J:I) and ell-1 residual intersection and
    -- M = I^r*(R^1/K)
    R := ring I;
    d := degree(I_0);
    (sI,ell,r) := specialFiberInfo(I,I_0);
     <<(ell,r)<<endl;flush;
    kk := ultimate(coefficientRing, ring I);
    choose1 = I -> sum(I_*, i-> random(kk)*i);
    J = ideal apply(ell-1, choose1 I);
--    J := rand(I,ell-1,d);
    (J:I, prune(I^r*(R^1/K)))
    )

isIsoWithMap = (A,B)->(
    S := ring A;
    H := Hom(A,B);
    Hp := prune H;
    pmap := Hp.cache.pruningMap;
    f := homomorphism(pmap*map(Hp,S^1, random(target presentation Hp,S^1)));
    t := if prune coker f == 0 then true else false;
    (t,f))

isHomogeneousIso = (A,B)->(
        if not isHomogeneous A and isHomogeneous B then error"inputs not homogeneous";
    	S := ring A;
	A1 := prune A;
	B1 := prune B;

	--handle the cases where one of A,B is 0
	isZA1 = A1==0;
	isZB1 = B1==0;	
    	if isZA1 =!= isZB1 then return false;
	if isZA1 and isZB1 then return true;

	-- from now on, A1 and B1 are nonzero
	dA := degree A1_*_0;
	dB := degree B1_*_0;
	df := dB-dA;
        H := Hom(A1,B1);       
	kk := ultimate(coefficientRing, ring A);
	sH := select(H_*, f-> degree f == df);
	if #sH ==0 then return false;
	g := sum(sH, f-> random(kk)*homomorphism matrix f);
	kmodule := coker vars S;
	gbar := kmodule ** g;
	if gbar==0  then return false;
--	error();
	(prune coker gbar) == 0 and prune ker g == 0
	)
	

isLocalIso = (A,B)->(
    if isHomogeneous A and isHomogeneous B and
            all(A_*, a->degree a == degree(A_*_0)) and 
	    all(B_*, a->degree a == degree(B_*_0)) then
	return isHomogeneousIso(A,B);

	S := ring A; 
	kk := ultimate(coefficientRing, S);
	kmod := coker vars S;
	A1 := prune A;
	B1 := prune B;

--handle the cases where one of A,B is 0
	isZA1 = A1==0;
	isZB1 = B1==0;	
    	if isZA1 =!= isZB1 then return false;
	if isZA1 and isZB1 then return true;

--now we can assume both are nonzero
        H1 := Hom(A1,B1);      
	if #H1_* == 0 then return false;
	g1 := sum(H1_*, f-> random(kk)*(kmod**homomorphism matrix f));
	t1 = (prune coker g1 == 0);
	if t1 == false then return false else(
	    <<"there is a surjection arg1 -> arg2"<<endl;
            H2 := Hom(B1,A1);      
	    if #H2_* == 0 then return false;	    
	    g2 := sum(H2_*, f-> random(kk)*(kmod**homomorphism matrix f));
	    prune coker g2 == 0)
	)

///
restart
load "residualDeterminantal.m2"
kk = ZZ/101
S = kk[x,y]
A = subquotient(matrix{{x}}, matrix{{x^2,y}})
prune A
B = S^{-2}**A
B' = B++B**S^{3}
isLocalIso(A,B)
isLocalIso(A,B')
isLocalIso(B',A)

isHomogeneousIso(A,B)
isHomogeneousIso(A,B')
isHomogeneousIso(B,A)

isLocalIso(A++A, A++S^{2}**A)
///
///
restart
load "residualDeterminantal.m2"
(p,n) = (2,4)
q = n-p
s = p*q
r = p*q+1-p-q
ell = s+1

I = detPower(p,n,1);
(sI,ell,r) = specialFiberInfo(I,I_0)

time (K,M) = conj I;
minimalBetti M -- CM codim 
time M' = Ext^4(M,(ring M)^1)
time M'' = prune fastExt(4, M)
isHomogeneousIso(M'',coker vars ring M)
isHomogeneousIso(coker vars ring M, M'')
isHomogeneousIso(M'', M)
isHomogeneousIso(M, M'')

isLocalIso(M'',coker vars ring M)
isLocalIso(coker vars ring M, M'')
isLocalIso(M'', M)
isLocalIso(M, M'')
///


GConditions = I->(
    p := presentation prune module I;
    c := codim I;
    apply(numrows p - c + 2, i-> codim minors(i+1,p))
	)
	
///
--look at depths of powers: (stab at value = analyt spread = (pn -p^2+1). 
--Note red num = pq-p-q+1 = (p-1)n-p^2+1
(p,n) = (2,5) -- runs out of Heap for 3,6
num = 2
cod = n-p+1
I = apply(num, j->detPower(p,n,j+2));
apply (num, j->(
time	print pdim minimalBetti ((ring I_j)^1/I_j);
	flush;))
apply(num, j-> prune fastExt(cod+j+2,I_j))
--results: set q := n-p
--2 x 4 matrix: R/det^i has depth 3 for all i>=2.
--2 x 5 matrix: R/det^i has depth 3 for all i>=2. pd's 7,7...
--2 x 6 matrix: R/det^i has pd 9 for all i>=2.
--3 x 5 -- pd's are 3,5,7,7...
--3 x 6 -- pd's 4,7,10...-- 
///


--Notation: 
--ell = analyt spread I
--r = reduction number I
--K = (J:I) = (ell-1)-residual intersection, 
--Ibar = I*(S^1/K)

-- (a) M := I^r/J*I^(r-1) or M := Ibar^r is MCM of codim ell-1;
-- (b) M \cong I^(r+j)/J*I^(r+j-1) or Ibar^(r+j) for j>=0
-- (c) M is omega_{R/K} - self-dual. (sometimesthis isomorphism seems strange and/or inhomogeneous)
-- (d) M \cong Hom(M,M) (sometimes this isomorphism seems strange and/or inhomogeneous)
--In some cases also:
-- (e) M \cong omega_{R/K}

--the following function prepares K, Mbar, and returns true iff Mbar \cong M=I^r/JI^{r-1}
prepare = method()
prepare Ideal  := I->(
time (sI,ell,r) = specialFiberInfo(I,I_0);
s = ell-1;
if r == 0 then error"the ideal has analytically independent generators";
(K,M) = conj I;
s' := codim K;
if s' !=s then error "doesn't form an ell-1 residual intersection";
geom:= codim(I+K);
if geom > s then <<"geometric residual" else << "not geometric"<<endl;
R = ring K;
Mbar = prune(I^r*(R^1/K));
isHomogeneousIso(M,Mbar))

prepare (Ideal, Ideal, ZZ,ZZ)  := (I,J,ell,r) ->(
s = ell-1;
K = (J:I);
M = module(I^r)/module(J*I^(r-1));
--(K,M) = conj I;
s' := codim K;
if s' !=s then error "doesn't form an ell-1 residual intersection";
geom:= codim(I+K);
if geom > s then <<"geometric residual" else << "not geometric"<<endl;
R = ring K;
Mbar = prune(I^r*(R^1/K));
isHomogeneousIso(M,Mbar))

isEquigenerated = I ->(
    degs := I_*/degree;
    if isHomogeneous I and  all(degs, i-> i==degs_0) then true else false)


-- (a) M := I^r/J*I^(r-1) or M := Ibar^r is MCM of codim ell-1;
isMbarMCM = ()->if  isEquigenerated I then (print (B = minimalBetti Mbar);
                                       return(s+1 == #totalBetti B)
				       ) else(
				    Ko := koszul vars R;
				    MKo = Mbar**Ko;
				    B = apply(1+ length Ko, i-> numgens prune HH_i MKo);
                                    print B;
				    #select(B, i -> i!=0) == s+1)

-- (b) M \cong I^(r+1)/J*I^r or Ibar^(r+1)
isIsoNextPower = () -> if isEquigenerated I then return isHomogeneousIso(Mbar,I^(r+1)*(R^1/K)) else
                                              isLocalIso(Mbar,I^(r+1)*(R^1/K))

--(c) M is omega_{R/K} - self-dual. 
isSelfDual = ()->if isEquigenerated I then 
    (Mbar' = prune fastExt(ell-1, Mbar);
    return isHomogeneousIso(Mbar,Mbar')) else
    (Mbar' = Ext^(ell-1)(Mbar, (ring Mbar)^1);
    isLocalIso(Mbar,Mbar'))

-- (d) M \cong Hom(M,M) (sometimes this isomorphism seems strange and/or inhomogeneous)
isIsoEnd = ()-> if isEquigenerated I then return isHomogeneousIso(Mbar, Hom(Mbar,Mbar)) else
                                            isLocalIso(Mbar, Hom(Mbar,Mbar))

-- (e) M \cong omega_{R/K}
isIsoOmega  = ()-> if isEquigenerated I then return isHomogeneousIso(Mbar, Ext^s(R^1/K, R^1)) else
                                             isLocalIso(Mbar, Ext^s(R^1/K, R^1))


reesIdeal1 = method(Options => {Variable => "w"})

fixupw = w -> if instance(w,String) then getSymbol w else w

reesIdeal1(Module) := Ideal => o -> M -> (
     P := presentation M;
     UE := transpose syz transpose P;
     symmetricKernel(UE,Variable => fixupw o.Variable)
     )

reesIdeal1(Ideal) := Ideal => o-> (J) -> (
     symmetricKernel(gens J, Variable => fixupw o.Variable)
     )

---- needs user-provided non-zerodivisor. 

reesIdeal1(Module, RingElement) := Ideal =>
reesIdeal1(Module, RingElement) := Ideal => o -> (M,a) -> (
     R := ring M;
     if R =!= ring a 
       then error("Expected Module and Element over the same ring");   
     P := presentation M;
     S := symmetricAlgebra(target P, VariableBaseName => fixupw o.Variable);
     I := ideal(vars S * promote(P,S));
     saturate(I,promote(a,S)))
reesIdeal1(Ideal, RingElement) := Ideal => o -> (I,a) -> (
     reesIdeal(module I, a)
     )

///
restart
load "residualDeterminantal.m2"

--A difficult Rees ideal
R = ZZ/101[a,b,c,d]
I = ideal(a^3*b^2*c^2-a^4*b*d^2+a^2*b^2*d^3-a*c^2*d^4,a^2*b^3*c^2-a^3*b^2*d^2+a*b^3*d^3-b*c^2*
       d^4,-a^3*b^3*c+a^2*b^4*c-a^3*b*c^2*d+a*b*c*d^4-b^2*c*d^4,-a^2*b*c^4-a^3*b^2*c*d+a^2*b^3*c*
       d+a*b^3*c*d^2-b^4*c*d^2,a*b^5*c-b^6*c+a*b^3*c^2*d-b*c^4*d^2-a*b^2*c*d^3+b^3*c*d^3)

mu = k -> (gens(I^k) % (I^(k-1))*(ideal vars R))
mu 2


P = presentation module I
(S,phi) = flattenRing (Sy = symmetricAlgebra(target P))
Iy =  phi ideal(vars Sy*promote(P,Sy))
S1 = ZZ/101[gens S]
(gens S1)/degree
psi = map(S1,S)
I1=(psi Iy)


A = psi phi promote(I_0,Sy)
isHomogeneous A
P2 = psi phi (ideal(vars Sy))^2
X = psi phi ideal promote(vars R, Sy)
J72 = intersect(X^7, P2);
betti oo

syzA = syz contract(gens(X^7), A);
betti contract (gens(X^7),A)
cJ72 = map( S1^119,,contract(transpose (gens (X^7)*syzA), gens J72));
betti cJ72
scJ72 = syz (cJ72, DegreeLimit => 2);
rel = contract(A,gens J72)*scJ72;
ideal rel


J2 = intersect(P2,Iy);
betti J2
betti I
intersect(J2 , ideal A);


(Rflat,phi) =  flattenRing Sy

Aflat = phi A
Iyflat = phi Iy
verbose = 1
time (Iyflat : Aflat)
time (Iy : promote(I_0, Sy)) -- more than 486 sec

time saturate (Iy, promote(I_0, Sy), Strategy => Iterate)
///


jacDual = phi -> (
    --The 
    IX := trim ideal flatten entries Phi;
    n := numrows phi;
    m := numcols phi;
    if numgens IX > m then IX = ideal vars ring phi;
    X = gens IX;
    R = ring phi;
    S = R[T_1..T_n];
    T = vars S;
    XS := promote(X,S);
    B := T * promote(phi,S)//XS;
    assert(XS*B == T * promote(phi,S));
    B
    )

 
 ///
restart
load "residualDeterminantal.m2"
m = 3
R = ZZ/101[x_(0,0)..x_(m-1,m)]    
Phi = transpose genericMatrix(R,x_(0,0),m,m-1)
jacDual Phi

/// 
     
     
end--

----generic determinantal examples
--Summary:
--2 x n:
--part a for n<=6 (also 3 x 5)
--parts a,b,c,d,e checked for n<=5. 
--
--Note: for the maximal minors of a p x n generic matrix,
--g = n-p+1
--q = n-p
--s = p*q
--r = p*q+1-p-q
--ell = s+1
-- ell-g = p*q-q 
--so, sincd p>=2, we have  ell-g > r
restart
load "residualDeterminantal.m2"
(p,n) = (2,4)
I = detPower(p,n,1);
prepare I
isMbarMCM() == true
isIsoNextPower() == true
isSelfDual() == true
isIsoEnd() == true
isIsoOmega() == true
-------------------------
--some monomial ideals
restart
load "residualDeterminantal.m2"
S = ZZ/101[a,b,c,d]    
I = ideal"ab,ac,bc,bd,d2"
codim I == 3 -- this is g
prepare I
(ell,r) == (4,2) --geometric so ell-g < r
isMbarMCM() == true
isIsoNextPower() == true
isSelfDual() == true
isIsoEnd() == true
isIsoOmega() == false

I = ideal"ab2,ac2,bc2,bd2,d3"
codim I ==3 --- again, ell-g < r.
prepare I
(ell,r) == (4,3) -- not geometric
isMbarMCM() == true
isIsoNextPower() == true
isSelfDual() == true
isIsoEnd() == true 
isIsoOmega() == true

------------------------
--some non-generic p x p+1
--3 x 5 non-generic in 8 vars
restart
load "residualDeterminantal.m2"
S = ZZ/101[a..h]
m = matrix"a,b,c,d,e;
       b,c,h,e,f;
       c,d,e,f,g"
I = minors(3,m)       
codim I == 3 -- in this case ell-g > r
prepare I -- 40sec. --geometric residual
(ell,r) = 7,2
isMbarMCM() == true
isIsoNextPower() == true
isSelfDual() == true
isIsoEnd() == true
isIsoOmega() --true

---------------------------------
--4 x 5 non-generic in 4 vars
restart
load "residualDeterminantal.m2"
S = ZZ/101[a..d]

{*
L = flatten entries gens((ideal vars S)^2)
setRandomSeed 0
randm = ()->(
m := mutableMatrix map(S^4, S^{5:-2},(i,j)-> if i>j+1 or j>i+2 then 0_S else L_(random 10));
apply (4, i-> m_(i,i) = S_i^2);
m_(3,2) = 0;
m_(3,3) = a;
m_(3,4) = b;
m = matrix m;
mi := apply(4, i->minors(i+1, m));
(m, mi/codim)
)
M=apply (1000, i->(
	(m, seq) = randm();
	if seq == {4,4,3,2} then (
	return m;
	break))
);
M1 = select(M, i-> i =!=null);
m = M1_0
*}
m = matrix {{a^2, d^2, b^2, 0, 0}, {d^2, b^2, b*d, c^2, 0}, {0, a*d, c^2, b*c, b*c}, {0, 0, 0,
      a, b}}
I = minors(4,m);
codim I == 2
time prepare I -- computation of the special fiber did not finish in 10 hours.
(ell,r) 
isMbarMCM() 
isIsoNextPower() 
isSelfDual() 
isIsoEnd() 
isIsoOmega()

-----------------------------------------
--3 x 4 non-generic in 3 vars
{*
restart
load "residualDeterminantal.m2"
S = ZZ/101[a..c]
L = flatten entries gens((ideal vars S)^2)
randm = ()->(
m := mutableMatrix map(S^3, S^{4:-2},(i,j)-> if i>j+1 then 0_S else L_(random 6));
apply (3, i-> m_(i,i) = S_i^2);
m_(2,1) = 0;
m_(2,2) = a;
m_(2,3) = b;
m = matrix m;
mi := apply(3, i->minors(i+1, m));
(m, mi/codim)
)

randm()
M=apply (1000, i->(
	(m, seq) = randm();
	if seq == {4,4,3,2} then (
	return m;
	break))
)
M1 = select(M, i-> i =!=null)
m = M1_0
*}

--An example found by the method above:
restart
load "residualDeterminantal.m2"
S = ZZ/101[a..c]
m = matrix {{a^2, a*c, c^2, c^2}, {a*b, b^2, c^2, a^2}, {0, 0, a, b}}
I = minors(3,m)
betti I -- generated by 5 quintics
codim I == 2
prepare I -- ell-g = 1 < r
(ell,r) ==(3,7) --is geometric, Ibar^r \cong I^r/JI^(r-1)
isMbarMCM() == true
isIsoNextPower() == true
isSelfDual() == true
isIsoEnd() == true
isIsoOmega() ==false

--minimalBetti module K -- bug!


T = S/K
--the code below implements the omega-self-duality of M = I^7*T 
--and the isomorphism Hom(M,M) \cong M
--as equalities of ideals in T.
--Note that the multipliers have incomprehensible degrees.

toT = map(T,S)
Ibar = trim toT I
f = Ibar_0    
f = rand(Ibar,1,5)
f1 = rand(Ibar,1,5)

gens(Ibar^8) % (f*Ibar^7) == 0
gens(Ibar^7) % ((f^7*Ibar):Ibar^7) ==0
gens((f^(7)*Ibar^7):Ibar^7) % (Ibar^7) ==0

gens((f^13*Ibar):Ibar^7) % (Ibar^7) ==0
gens((Ibar^7)) %((f^13*Ibar):Ibar^7)  !=0

gens((f^12*Ibar):Ibar^7) % (Ibar^7) !=0
gens((Ibar^7)) %((f^12*Ibar):Ibar^7)  ==0

g = rand((f^7*Ibar^7): (((f^7*Ibar):Ibar^7)),1,62)
(f^7*Ibar^7) == g*((f^7*Ibar):Ibar^7)

g1 = rand(Ibar,1,62);
(f^7*Ibar^7) == g1*((f^7*Ibar):Ibar^7)

------------------
--attempt to find a 3 x 4 non-generic in 4 vars that really involves all 4, has ell = 3
--with r>0
--so far this failed.
restart
load "residualDeterminantal.m2"
S = ZZ/101[a..d]
setRandomSeed 0

L = flatten entries gens((ideal vars S)^2)
randm = ()->(
m := mutableMatrix map(S^3, S^{4:-2},(i,j)-> if i>j+1 then 0_S else L_(random 10));
apply (3, i-> m_(i,i) = S_i^2);
m_(2,1) = 0;
m_(2,2) = a;
m_(2,3) = b;
m = matrix m;
mi := apply(3, i->minors(i+1, m));
(m, mi/codim)
)

M=apply (100, i->(
	(m, seq) = randm();
	if seq == {4,3,2} or seq =={3,3,2} then (
	return m;
	break))
)
M1 = select(M, i-> i =!=null)

M2 = select(M1, m->(
I = minors(3,m);
(sI,ell,r) = specialFiberInfo(I,I_0);
(ell == 3) and r>0 )
)

---------------
--monomial curve examples
--in P3:
restart
load "residualDeterminantal.m2"

S = ZZ/32003[a..d]
I = monomialCurveIdeal(S,{1,3,4}) -- the smooth rational quartic in P3
--note that in this case the residual we take is inhomogeneous!

prepare I 
(ell,r) ==(3,1) -- codim 2, I not CM, geometric residual, and Ibar \cong I/J
isMbarMCM() == true
isIsoNextPower() == true
isSelfDual() == true
isIsoEnd() == true
isIsoOmega() ==false


-------------------------
--rational normal curves (deg = d-1 >=4)
restart
load "residualDeterminantal.m2"
--results as below fro d= 5,6, maybe 7
d = 6
S = ZZ/32003[x_0..x_(d-1)]
I = monomialCurveIdeal(S,toList(1..d-1))

prepare I 
(ell,r) --for d= 5,6,7 get  (5,1), (6,3), (7,3); geometric residual, Ibar^r \cong I^r/JI^(r-1).
--ell-g = r for d=5, ell-g < r for d = 6
isMbarMCM() == true
isIsoNextPower() == true
isSelfDual() == true
isIsoEnd() == true
isIsoOmega() ==false

--
--rational curve with triple cusp in P4
restart
load "residualDeterminantal.m2"

d = 5
delta = 3
S = ZZ/32003[x_0..x_(d-1)]
exps = toList(1..d-2)|{d-1+delta}
I = monomialCurveIdeal(S,exps)
codim I == 3 -- 
betti res I -- Cohen-Macaulay

prepare I 
(ell,r) = (4,2) -- ell-g =1 <r
isMbarMCM() == true 
isIsoNextPower() == true
time isSelfDual() == true -- uses inhomogeneous J
isIsoEnd() == ? -- slow
isIsoOmega() ==false


----------------------------
--residual intersection in a codim 2 perfect
restart
load "residualDeterminantal.m2"
d = 4; n= 5;e = 1; kk = ZZ/101
S = kk[x_0..x_(d-1)]
--
{*
m = map(S^n,S^{n+1:-e}, (i,j) -> if i<n-1 then random(kk)*x_(random(d)) else random(kk)*x_(random(d))^2)
minorss = apply(n, j->minors(j+1,m));
minorss/codim
*}
--found with this technology
m = matrix {{11*x_0, -16*x_2, -50*x_0, -26*x_0, -26*x_1, 0}, {35*x_1, 11*x_3, -15*x_0, -x_3, -13*x_1,
      -26*x_0}, {12*x_2, 5*x_1, -9*x_3, 19*x_0, -33*x_3, -21*x_3}, {33*x_1, -29*x_1, 40*x_3, -34*x_0, 12*x_2,
      40*x_1}, {40*x_0, -47*x_1, 49*x_1, 33*x_2, 25*x_3, 0}}
--5 x 6 matrix
I = minors(5,m);
codim I == 2

prepare I 
(ell,r) -- (4,3) -- ell-g = 2 < r
isMbarMCM() == true
isIsoNextPower() == true
isSelfDual() == true
isIsoEnd() == true
isIsoOmega() ==false

--------------
--isSelfDual can fail with 1-residual int of a codim 2 perfect ideal:
restart
load "residualDeterminantal.m2"
S = ZZ/101[x,y]
P = ideal vars S
--mlin =  random(S^1, S^{2:-1})
--mquad =  random(S^2, S^{2:-2})
--m = mlin||mquad
m = matrix"x2,0,y;0,y2,x"
isHomogeneous m
I = minors(2,m)
prepare I 
(ell,r) == (2,1)
isMbarMCM() == true
isIsoNextPower() == true
isSelfDual() == false
isIsoEnd() == true
isIsoOmega() ==false

--Bernd proves that for a perfect codim 2 ideal I with r= 1, such that
--Ibar is omega-self-dual, then the link L of I would have r = 1,
--which is not the case here.


--buta 2-residual intersection where it does work.
restart
load "residualDeterminantal.m2"
S = ZZ/101[x,y,z]
mlin =  random(S^2, S^{3:-1})
mquad =  random(S^2, S^{3:-2}) -- get the 0 value in the assert for up to -8
m = mlin||mquad
I = minors(3,m) -- 3x3 of a 3x4 matrix, codim 2, perfect

prepare I 
(ell,r) == (3,2) -- geometric residual, ell-g = 1 <r
isMbarMCM() == true
isIsoNextPower() == true
isSelfDual() == true
isIsoEnd() == true
isIsoOmega() ==false


restart
load "residualDeterminantal.m2"
S = ZZ/101[x,y,z]
mlin =  random(S^3, S^{3:-1})
mquad =  random(S^3, S^{1:-3})
m = mlin|mquad
I = minors(3,m) -- 3x3 of a 3x4; codim 2, perfect

prepare I 
(ell,r) == (3,2) -- ell-g= 1<r
isMbarMCM() == true
isIsoNextPower() == true
isSelfDual() == true
isIsoEnd() == true
isIsoOmega() ==false


-----------------------
--monomial ideals. Must have codim <= ell-1 < mu (so not primary to the max ideal), 
--and have an (ell-1)-residual intersection.

restart
load "residualDeterminantal.m2"
setRandomSeed 0
(mu,deg) = (6,3)
S = ZZ/101[a..d]
I = randomMonomialIdeal(toList (mu:deg),S)
toString I
codim I
(sI, ell, r) = specialFiberInfo(I,I_0)

J = rand(I,deg,ell-1)
K = (J:I)
codim K ==  ell-1

S = ZZ/101[a..d]
I = ideal(b^2*c,a^2*b,b^3,a*c^2,a*c*d,a^2*c)
codim I ==2
betti res I -- pd 4
prepare I -- Mbar not cong M. Not geom residual
(ell, r) == (4,3) -- ell-g = 2 < r
isMbarMCM() ==true
isIsoNextPower() == true
isSelfDual() ==true
isIsoEnd()  == true
isIsoOmega() == false

--a linkage case in a codim 3 ideal
restart
load "residualDeterminantal.m2"
(mu,deg) = (6,3)
S = ZZ/101[a..d]
I = ideal(d^3,c*d^2,c^3,b^3,a^2*c,a*c^2)
codim I ==3
betti res I -- pd 4
prepare I -- Mbar is cong M. is geom residual
(ell, r) == (4,3)
isMbarMCM() == true
isIsoNextPower() == true
isSelfDual() == true
isIsoEnd()  == true
isIsoOmega() == false
------------------------------------------
--Bernd's counter-example to self-duality, from July 8.
restart
load "residualDeterminantal.m2"
S = ZZ/101[x,y,z]
{*
mlin =  map(S^3, S^{-1},matrix"x;y;z")
mquad =  random(S^3, S^{3:-2})
mrand = mlin|mquad
Irand = minors(3,mrand)
prepare Irand -- SLOW
*}

--the following specialization makes the computation quick
m = map(S^3, S^{-1,3:-2}, 
    matrix"
    x, y2,z2,0;
    y, x2,y2,z2;
    z, 0, x2,y2")
apply(3, i->codim minors(i+1,m)) -- {3,3,2}
I = minors(3,m)

prepare I -- computation with m1 takes a few minutes, but with m it's quick
(ell,r) == (3,2) --its a geometric residual intersection, and Ibar is \cong I^2/JI
--ell-g = 1 < r
isMbarMCM() == true --total betti numbers are 3,6,3 -- note that this is symmetric.
isIsoNextPower() == true
isSelfDual() == false
isIsoEnd() == true
isIsoOmega() ==false


restart
load "residualDeterminantal.m2"
d = 4
S = ZZ/101[x_0..x_(d-1)]
m1 = transpose vars S**S^{-1}
m2 = map(S^d, S^{d:-2}, (i,j) -> (if i>j then x_(i-j-1)^2 else
	                          if i == j then x_(d-1)^2 else 0_S)
			          )	    	    	    	  
m = m1 |m2
I = minors(d,m)
GConditions I
--perfect, codim 2
prepare I -- computation with m1 takes a few minutes, but with m it's quick
(ell,r) == (d,  d-1 = ell-g+1) --its a geometric residual intersection, and Ibar is \cong I^2/JI
--here ell-g =1 <r
--ell-g = 1 < r
isMbarMCM() == true --total betti numbers are d times the binomial coefficients -- note that this is symmetric.
--Total Betti Number {4, 12, 12, 4, 0}
isIsoNextPower() == true
isSelfDual() == false
isIsoEnd() == true
isIsoOmega() ==false



{*
Let d \geq 2 and let I be the ideal in the polynomial ring in d variables
generated by the d by d minors of a d+1 by d matrix whose first row
has the d variables as entries and the other entries are suitable (if not
general) quadrics. Again, \ell=d and r=d-1. But I^{d-1}/J_{d-1}I^{d-2}
cannot be omega-selfdual because the general d-residual intersection
is the maximal ideal, which cannot have reduction number 1 modulo
the general d-1-residual intersection because the d-1-residual intersection
has initial degree 3.

M is always isomorphic to its endomorphism ring in these examples
because M is S_2 and the general d-1-residual intersection has no
codimension d associated primes.

I think there is just a distinction between small and large reduction number.
If r is at most \ell-g, everything may be true. Otherwise the selfduality can
fail, although we have seen it hold in many cases, even for very large reduction
numbers. It would be good to understand this.
*}

restart
load "residualDeterminantal.m2"
d = 

--Bernd's counter-example to self-duality, from July 8.
restart
load "residualDeterminantal.m2"
S = ZZ/101[x,y,z]
{*
mlin =  map(S^3, S^{-1},matrix"x;y;z")
mquad =  random(S^3, S^{3:-2})
mrand = mlin|mquad
Irand = minors(3,mrand)
prepare Irand -- SLOW
*}

--the following specialization makes the computation quick
m = map(S^3, S^{-1,3:-2}, 
    matrix"
    x, y2,z2,0;
    y, x2,y2,z2;
    z, 0, x2,y2")
apply(3, i->codim minors(i+1,m)) -- {3,3,2}
I = minors(3,m)

prepare I -- computation with m1 takes a few minutes, but with m it's quick
(ell,r) == (3,2) --its a geometric residual intersection, and Ibar is \cong I^2/JI
--ell-g = 1 < r
isMbarMCM() == true --total betti numbers are 3,6,3 -- note that this is symmetric.
isIsoNextPower() == true
isSelfDual() == false
isIsoEnd() == true
isIsoOmega() ==false


-----
restart 
load "residualDeterminantal.m2"
S = ZZ/101[a,b,c]
m = matrix"a,b,c,0;
           0, a, b, c;
	   0,bc,ac,ab"
I = minors(3,m)
codim I
codim minors(2,m)
isHomogeneous I


prepare I
(ell, r) == (3,4)
isMbarMCM() == true --total betti numbers are 3,6,3 -- note that this is symmetric.
isIsoNextPower() == true
isSelfDual() == true
isIsoEnd() == true
isIsoOmega() ==false
J3 = ideal random(S^1,S^{3:-4});
J2 = ideal (J3_0,J3_1);
isHomogeneousIso (Mbar, module(J3:I)/module(J2:I)) == false

----
restart 
load "residualDeterminantal.m2"
S = ZZ/101[a,b,c]
m = matrix"a,b,c,0;
           0, a2, b2, c2;
	   0,bc,ac,ab"
I = minors(3,m)
prepare I
(ell,r) == (3,7) -- (was (3,4) for the two linear row case)
isMbarMCM() == true --total betti numbers are 3,6,3 -- note that this is symmetric.
isIsoNextPower() == true
isSelfDual()  == true
isIsoEnd() == true
isIsoOmega() ==false


----
--random ideals
restart 

test = I-> (
    <<betti res I<<endl;
    <<"--prepare and report (ell, r) and whether Ibar^r cong I^r/JI^(r-1)"<<endl;
t := prepare I;
<<endl <<"? Ibar^r cong  I^r/JI^(r-1) "<<t <<endl;
<<"betti numbers of Mbar: ? Is Mbar MCM "<<endl;
<<isMbarMCM()<<endl;
<<"? Mbar is self-dual: "<<endl;
<<isSelfDual()<<endl;
<<"? Mbar cong End Mbar: "<<endl;
<<isIsoEnd()<<endl;
<<"? Mbar cong omega: "<<endl;
<<isIsoOmega();
)

load "residualDeterminantal.m2"
S = ZZ/101[a,b,c,d]
I1 = ideal"a,b"
I = ideal ((gens I1)*random(source gens I1, S^{5:-2}))
test I


isMbarMCM(); == true --total betti numbers are 3,6,3 -- note that this is symmetric.
isIsoNextPower() == true
isSelfDual()  == true
isIsoEnd() == true
isIsoOmega() ==false

