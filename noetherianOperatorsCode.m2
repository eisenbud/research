------- Computation of Differential Primary Decompositions
--------------------------------------------------------------------------
--------------------------------------------------------------------------


--- Computes the join of two ideals
joinIdeals = (J, K) -> 
(
    v := symbol v; 
    w := symbol w;
    R := ring J;
    n := numgens R;
    T := (coefficientRing R)[v_1..v_n, w_1..w_n];
    Q := ((map(T, R, toList(v_1..v_n))) J) + ((map(T, R, toList(w_1..w_n))) K);
    S := T / Q;
    F := map(S, R, apply(n, j -> v_(j+1) + w_(j+1)));
    ker F     
) 

-- Auxiliary function to introduce a polynomial ring that is used to represent differential operators
-- Given a polynomial ring R=k[x_1,..,x_n], it reutrns another polynomial ring R[dx_1,..,dx_n]
memoRing = memoize( (R,diffVars) -> R(monoid[diffVars]))
diffAlg = (R) -> (
    diffVars := apply(gens R, i -> value("symbol d" | toString(i)) );
    memoRing(R,diffVars)
)


--- This function returns the ring we shall use to parametrize the punctual Hilbert scheme
getHilb = (P, depVars) -> (
    R := ring P;
    varsHilb := apply(depVars, i -> value("symbol h" | toString(i)) );
    S := (frac(R/P))(monoid[varsHilb]);
    S
)

-- This map receives an ideal Q in R=QQ[x_1..x_n] primary to a maximal ideal P
-- and it returns an ideal I in S=(frac(R/P))[y_1..y_c] which is primary with respect to (y_1..y_c).
mapRtoHilb = (Q, P, S, depVars, indVars, m) -> (
    R := ring Q;
    n := numgens R;  
    if m == 0 then (      
   	-- compute the exponent that determines the order of the diff ops
    	while not isSubset(P^m, Q) do m = m + 1;
    ); 	        
    -- map from R into the "base changed" module of principal parts
    diag :=  ideal apply(depVars, w -> value(value("symbol h" | toString(w)))_S );
    L := apply(gens R, w -> if any(indVars, z -> z == w) 
	               then sub(w, S) else sub(w, S) + value(value("symbol h" | toString(w)))_S);
    mapRtoS := map(S, R, L);
    ideal mingens ((mapRtoS Q) + diag^m)    
)

-- Auxiliary function to lift differential operators
liftNoethOp = (A, R, D) -> (
    FF := coefficientRing ring A;
    L := apply(flatten entries last coefficients A, 
	           w -> lift(denominator(sub(w, FF)),R));
    m := if L == {} then 1_R else lcm L;	       
    sub(m*A, D)
)  

-- Auxiliary function used in the inverse system function
unpackRow = (row, FF) -> (
   (mons, coeffs) := coefficients row;
   sub(coeffs, FF)
)    

-- This function returns a set of Noetherian operators given the ideal I in the punctual Hilbert scheme
-- that parametrizes the primary ideal Q.
invSystemFromHilbToNoethOps = (I, R, S, depVars) -> (
    mm := ideal vars S; -- maximal irrelevant ideal of S
    m := 0; -- compute the exponent that determines the order of the diff ops
    while not isSubset(mm^m, I) do m = m + 1;
    FF := coefficientRing S; 
    allMons := basis(0, m-1, S); 
    gensI := flatten entries mingens I;
    diffMat := unpackRow(diff(gensI_0, allMons), FF);
    for i from 1 to length gensI - 1 do (
	auxMat := unpackRow(diff(gensI_i, allMons), FF);
	diffMat = diffMat || auxMat;
     );
    noethOps := flatten entries (allMons * mingens ker diffMat);  
    noethOps
)
   
-- This function can compute the Noetherian operators of a primary ideal Q.
-- Here we pass first through the punctual Hilbert scheme 
getNoetherianOperatorsHilb = Q -> (
    R := ring Q;
    P := radical Q;
    indVars := support first independentSets P;
    depVars := gens R - set indVars;	
    S := getHilb(P, depVars);
    I := mapRtoHilb(Q, P, S, depVars, indVars, 0);
    noethOps := invSystemFromHilbToNoethOps(I, R, S, depVars);
    diffVars := apply(depVars, w -> value("symbol d" | toString(w)));
    W := (coefficientRing S)(monoid[diffVars]);
    D := diffAlg(R);
    mapStoW := map(W, S, gens W);
    apply(noethOps, w -> liftNoethOp(mapStoW(w), R, D))       
) 


-- Auxiliary function to compute a basis for L2 / L1
findCompBasis = (L1, L2, S) -> (
    FF := coefficientRing S;
    allMons := unique(join(
	         flatten entries (coefficients(matrix{L1}))_0,
		 flatten entries (coefficients(matrix{L2}))_0)); 
    spanMat := sub((coefficients(matrix{L2}, Monomials => allMons))_1, FF);
    L := {};
    for w in L1 do (
	wMat := sub((coefficients(w, Monomials => allMons))_1, FF);
	if not isSubset(image(wMat), image(spanMat)) then
	    L = append(L, w);
	spanMat = spanMat | wMat;    
    );
    L
)


-- This function computes a "reduced set" of Noetherian operators that corresponds 
-- with the P-primary component (i.e., it assumes that we have already compute Noetherian
-- operators for all primary components corresponding to prime subideals of P).
getReducedSetNoetherianOperators = (I, P, pdI) -> (
    R := ring I;
    indVars := support first independentSets P;
    depVars := gens R - set indVars;	
    S := getHilb(P, depVars);
    IP := intersect(select(primaryDecomposition I, Q -> isSubset(radical(Q), P)));
    JP := saturate(IP, P);   
    m := 0;  -- compute the exponent that determines the order of the diff ops
    while not isSubset(intersect(JP, P^m), IP) do m = m + 1;
    L := if any(minimalPrimes I, P' -> P' == P) then (
       qq := mapRtoHilb(I, P, S, depVars, indVars, m);
       invSystemFromHilbToNoethOps(qq, R, S, depVars)
    ) else ( 
       J := saturate(I,P);  	
       aa := mapRtoHilb(I, P, S, depVars, indVars, m);
       bb := mapRtoHilb(J, P, S, depVars, indVars, m);
       L1 := invSystemFromHilbToNoethOps(aa, R, S, depVars);
       L2 := invSystemFromHilbToNoethOps(bb, R, S, depVars);
       findCompBasis(L1, L2, S)
    );   
    diffVars := apply(depVars, w -> value("symbol d" | toString(w)));
    W := (coefficientRing S)(monoid[diffVars]);
    D := diffAlg(R);
    mapStoW := map(W, S, gens W);
    apply(L, w -> liftNoethOp(mapStoW(w), R, D))          
)    


-- This function computes a differential primary decomposition 
-- with a number a differential operators equal to the 
-- arithmetic multiplicity. 
-- Input: an ideal I.
-- Output: a list of pairs (P_i,L_i) where P_i is an associated primes and 
--         and L_i is a list of differential operators.
solvePDE = I -> (
    AssI := ass I;
    pdI := primaryDecomposition I;
    L := {};
    for P in AssI do 
    	L = append(L, {P, getReducedSetNoetherianOperators(I, P, pdI)});
    L	
)


-- computes the annihilator ideal of a polynomial F in a polynomial ring 
-- Input: a polynomial. Output: a zero-dimension ideal that corresponds with the annihilator
polynomialAnn = (F) -> (
    deg := (degree F)_0;
    S := ring F;
    allMons := basis(1, deg + 1, S);
    diffMat := diff(allMons, F);
    (mons, coeffs) := coefficients diffMat;
    ideal mingens ideal (allMons * mingens ker coeffs)        
)

-- computes the annilihator of a vector space V of polynomials
-- typically one expects that V is close under differentiation
-- Input: a list which is a basis of V. Output: the ideal annihilator.
vectorAnn = (V) -> (
    intersect(apply(V, F -> polynomialAnn(F)))    
)    
  
--- Implements the inverse procedure of Noetherian operators
--- Given a prime ideal and a set of Noetherian operators, it computes the corresponding primary ideal
--- Input: L a list of Noetherian operators (inside R[dx_1,...,dx_n]); a prime ideal P.
--- Output: The corresponding primary ideal Q 
getIdealFromNoetherianOperators = (L, P) -> (
    R := ring P;
    indVars := support first independentSets P;
    FF := frac(R/P);
    D := ring L_0;
    S := FF[gens D];
    V := apply(L, F -> sub(F, S));
    I := vectorAnn(V);
    I = ideal apply(flatten entries gens I, f -> liftNoethOp(f, R, D));    
    X := D/(I+P);
    Lmap := apply(gens R, w -> sub(w, D) + value(value("symbol d" | toString(w)))_D);
    mapRtoX := map(X, R, Lmap);
    Q := ker mapRtoX;
    for v in indVars do -- heuristic for faster computation 
    	Q = saturate(Q, ideal(v));
    Prim := select(primaryDecomposition(Q), K -> radical(K) == P);
    Prim_0
) 



-- To this function we can pass the output of "solvePDE"
-- The output should recover the original ideal
getPDE = L -> (
    R := ring(L_0_0);
    I = ideal(1_R);
    for pair in L do (
	P := pair_0;
	Ldiff := pair_1;
	I = intersect(I, getIdealFromNoetherianOperators(Ldiff, P));
    );
    ideal mingens I
)

-- This function computes the arithmetic multiplicity of an ideal
amult = I -> sum apply(ass I, P -> degree(saturate(I,P)/I)/degree(P))

