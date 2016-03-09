newPackage(
"MCMApproximations",
Version => "0.9",
Date => "February 27, 2016",
Authors => {{Name => "David Eisenbud",
Email => "de@msri.org",
HomePage => "http://www.msri.org/~de"}},
Headline => "MCM Approximations and Complete Intersections",
DebuggingMode => true,
PackageExports => {"CompleteIntersectionResolutions2"}
)

export {
    "approximation", 
    "coApproximation",     
    "Total", -- option for approximation
    "CoDepth", -- option for approximation
    "approx", --synonym for approximation
    "layeredResolution",
    "auslanderInvariant",
    "profondeur", -- should be depth, but that's taken
    "regularitySequence", --regularities [add socle dimensions] of exts of successive CM approximation
    "syzygy",
    "socleDegrees",
    "setupRings",
    "Characteristic", -- option for setupRings
    "setupModules",
    "test" -- gives info on an example
    }

{* The following code crashes M2 v 8.2
S = ZZ/101[a]
R = S/ideal(a^2)
res (coker vars R, LengthLimit => 0)
*}


layeredResolution = method()
layeredResolution(Matrix, Module) := (ff, M) ->(
    --ff is a 1 x c matrix over a Gorenstein ring S
    --M is an S-module annihilated by I = ideal ff.
    --returns a pair (L,aug), where aug: L_0 \to M is the augmentation.
    --Here L_0 = L'_0 ++ B_0, and L' is the resolution of M', the 
    --MCM approximation of M over R' = S/(ideal ff'), and ff' = ff_{0..(c-2)}.
    L := null;
    cod := numcols ff;
    if cod <=1 then return (L = res M, map(M,L_0,id_(L_0)));
    S := ring ff;
    R := S/(ideal ff);
    ff' := ff_{0..cod-2};
    R' := S/(ideal ff');
    p:= map(R,R');
    q := map(R',S);
        
    MR := prune R**M;
    MR' := prune(R'**M);
    (alpha, beta) := approximation MR';
    B0 := source beta;
    M' := source alpha;
    pM' :=prune M';-- why isn't M' already pruned??

    pM'ToM' := (pM'.cache.pruningMap);
    M'TopM' := pM'ToM'^(-1);
    
    gamma := map(MR', pM'++B0, (alpha*pM'ToM')|beta);
    BB1 := ker gamma;
    B1 := minimalPresentation BB1;
--    assert(isFreeModule B1);
    psib :=  inducedMap(pM' ++ B0, BB1)*(B1.cache.pruningMap);
    psi := psib^[0];
    b := psib^[1];
--    assert(source psi == B1 and source b == B1);
--    assert(target psi == pM' and target b == B0);
    pM'S := pushForward(q,pM');
    bS := substitute(b,S);
    B0S := target bS;
    B1S := source bS;    
    KK := koszul(ff');
    B := chainComplex{bS};
    
    (L',aug') := layeredResolution(ff', pM'S);
    assert(target aug' == pM'S);
    psiS0 := map(pM'S, B1S, sub(matrix psi,S));
    psiS := psiS0//aug';
    Psi1 := extend(L',B[1],matrix psiS);
    Psi2 := Psi1**KK;
    Psi := extend(L',L'**KK, id_(L'_0))*Psi2;
    L = cone Psi; -- L', the target of Psi, is the first summand, so this is L_0==L'_0++B_0
    assert(L_0 == L'_0 ++ B_0);
    m := (sub((matrix alpha)*matrix pM'ToM',S)*matrix aug') |sub(matrix beta,S);
    aug := map(M,L'_0++B_0,m);
--Check exactness
--    scan(length L -1, s->assert( HH_(s+1) L == 0));

    (L,aug)
    )

///
restart
loadPackage("MCMApproximations", Reload =>true)
S = ZZ/101[a,b,c]
ff = matrix"a3, b3,c3" 
cod = numcols ff
I = ideal ff
R = S/I
q = map(R,S)
M0 = coker vars R
M0= coker random(R^2, R^{4:-1})

scan(5, s->(
M= pushForward(q,syzygy(s,M0));
<<time(L = (layeredResolution(ff, M))_0);<<endl;
print (betti L == betti res M);
))
///



socleDegrees = method()
socleDegrees Module := M ->(
    R := ring M;
    k := coefficientRing R;
    if not isField k then error"coefficient ring not a field";
     flatten degrees target basis Hom(coker vars R,M)    
    )
doc ///
   Key
    socleDegrees
    (socleDegrees, Module)
   Headline
    lists the degrees of the socle generators
   Usage
    L = socleDegrees M
   Inputs
    M:Module
   Outputs
    L:List
   Description
    Text
     L is the list of socle degrees of M, with multiplicities. Thus
     L = {} if the socle is 0.
    Example
     R = ZZ/101[x,y,z]
     M0 = R^1/(ideal(x,y,z)*ideal (x,y));
     M1 = coker random(R^{1,2}, R^{0,-1,-2}); -- dim 1
     M2 = coker random(R^{1,2}, R^{0,-1,-2,-4}); -- dim 0"
   SeeAlso
    regularitySequence
   ///
syzygy = method(Options=>{CoDepth => -1})
syzygy(ZZ,Module) := opts -> (k,M) -> (
    if k === 0 then return M;
    F := null;

    if k>0 then (
	F = res(M, LengthLimit => k+1);
	return coker F.dd_(k+1));
    
    if k<0 then (
	n := numgens ring M;
	if opts.CoDepth == 0 then
	n = 1 else
	if opts.CoDepth >0 then
	n = opts.CoDepth;
	F  = res(M, LengthLimit => n);
	M1 := image dual F.dd_(n);
	G := res(M1, LengthLimit => -k+n);
    return image dual G.dd_(-k+n));
    )
TEST///
     setRandomSeed 100;
     R = setupRings(2,2);
     M = syzygy_2 coker vars R_2;
     N = syzygy_2 syzygy(-2,M);
     assert(betti M == betti N)
     N = prune syzygy(-2,syzygy(2,M),CoDepth =>0);
     assert(betti M == betti N)
///

--<<docTemplate
doc ///
   Key
    CoDepth
   Headline
    Option for syzygy(-k,M,CoDepth => m)
   Description
    Text
     Allows the user to specify a number m (which must be at least CoDepth M),
     for more efficient computation.
   Caveat
    Does not check that the CoDepth value is correct.
   SeeAlso
    syzygy
///

doc ///
   Key
    syzygy
    (syzygy, ZZ, Module)
    [syzygy, CoDepth]
   Headline
    Produces the k-th syzygy module (k \in ZZ)
   Usage
    N = syzygy(k,M)
   Inputs
    k:ZZ
     which syzygy
    M:Module
   Outputs
    N:Module
   Description
    Text
     If k==0 then the N=M. If k>0 then the syzygy module is computed from the 
     resolution. If k<0 then the program returns the dual of the (n-k)-th syzygy
     of the dual of the k-th syzygy, where n is one more than Codepth if that
     opition is specified, and else n is the number of variables of ring M. 
     Of course the resulting N is 0 if ring M is regular, and otherwise correct
     only if ring M is Gorenstein. In the Gorenstein case, syzygy(-k, syzygy(k, M))
     -is the non-free part of the source of the MCM approximation of M.
    Example
     R = setupRings(4,3);
     M = coker vars R_2;
     betti res M
     betti syzygy(2,M)
     betti (N2 = syzygy(-2,M))
     betti res N2
     betti syzygy(-2,M,CoDepth=>2)
   Caveat
    ring M must be Gorenstein, and the program does not check
   SeeAlso
    setupRings
///
///
restart
loadPackage("MCMApproximations", Reload=>true)
///

///
restart
loadPackage("MCMApproximations", Reload =>true)
R = kk[a,b,c]/ideal(a^3,b^3,c^3)
M = coker vars R
res M	
syzygy(1,M)
betti res syzygy(-1,M)

c = 3
R =setupRings(c,3)
Rc=R_(c-1)
M0 = coker vars Rc
M0 = coker matrix{{Rc_0,Rc_1,Rc_2},{Rc_1,Rc_2,Rc_0}}

betti res (M0, LengthLimit=> 5)
M1 = prune syzygy(4, M0)
betti res M1
///

profondeur = method()
profondeur(Ideal, Module) := (I,M) ->(
    --requires R to be an affine ring (eg NOT ZZ[x])
    R := ring M;
    d := max(1,dim M); -- d=0 causes a crash
    if not isCommutative R then error"profondeur undefined for noncommutative rings";
    F := M**dual res (R^1/I, LengthLimit => d);
    i := 0;    
    while HH_i F == 0 do i=i-1;
    -i)

profondeur Module := M  ->(
    --profondeur of a module with respect to the max ideal, via finite proj dim
    --gives error if the ultimate coeficient ring of R = ring M is not a field.
    R := ring M;
    if not isCommutative R then error"profondeur undefined for noncommutative rings";
    (S,F) := flattenRing R;
    if not isField coefficientRing S then error"input must be a module over an affine ring";
    S0 := ring presentation S;
    r := F*map(S,S0); 
    MM := pushForward(r,M);
    numgens S0 - pdim MM)

profondeur Ring := R -> profondeur R^1

///
restart
loadPackage("MCMApproximations", Reload=>true)
///
doc ///
   Key
    profondeur
    (profondeur,Ideal,Module)
    (profondeur, Module)
    (profondeur, Ring)
   Headline
    computes the profondeur with respect to an ideal
   Usage
    m = profondeur (I,M)
   Inputs
    I:Ideal
    M:Module
    R:Ring
   Outputs
    m:ZZ
   Description
    Text
     When the ideal I is not specified, the maximal ideal is used, and the 
     computation is done using the Auslander-Buchsbaum formula.
///
TEST///
setRandomSeed()
R = kk[a,b,c,d,e]/(ideal(a,b)*ideal(c,d))
assert(profondeur R == 2)    
assert(profondeur(ideal(a,d,e), R^1) == 2)
assert(profondeur R^1 == 2)
/// 

--MCM approximation 
approximatione = method(Options =>{CoDepth => -1})
approximatione(ZZ,Module) := opts -> (n,M) ->(
    --returns the map to M from the
    --dual of the n-th syz of the n-th syzy of M
    --n = dim ring M - depth M +1 -- this just slows things down!
    F := res(M, LengthLimit =>n);
    G := res(coker transpose F.dd_n, LengthLimit =>n);
    F' := chainComplex reverse apply(n, j-> transpose F.dd_(j+1));
    phi := extend(G, F', id_(G_0));
    map(M, coker transpose G.dd_n, transpose phi_n)
)

///
restart
loadPackage("MCMApproximations", Reload =>true)
R = ZZ/101[a,b,c]/ideal(a^3,b^3)
Rc = R/ideal(b^3, c^3) 
M = prune pushForward(map(Rc,R), coker matrix"a,b,c;b,c,a")
n= 3
betti res syzygy_1 M
///
--<<docTemplate

approximatione Module := opts -> M ->(
    --returns the map from the essential MCM approximation
    n := 1+dim ring M;
    if opts.CoDepth == 0 then n = 1;
    if opts.CoDepth > 0 then n = opts.CoDepth;
    approximatione(n, M)
    )

coSyzygyChain = method()
coSyzygyChain(ZZ, Module) := (n,M) ->(
    --assuming M is MCM, the script returns
    --produces dual G of the  resolution of the dual of the second syzygy of M for n+1 steps,
    --adjusted so that M == image G.dd_0. Thus the map G.dd_(-1) is the universal map
    --of M into a free module, etc.
    F := res(M,LengthLimit => 1);
    G := res(coker dual F.dd_1, LengthLimit => n+1);
    H := (dual G) [-1];
    H)
    
coApproximation = method(Options =>{Total => true, CoDepth=>-1})
coApproximation Module := opts -> M -> (
    p := presentation M;
    F0 := target p;
    (phi,psi) := approximation(M, Total => opts.Total,CoDepth => opts.CoDepth);
    M' := source (phi|psi);--the total MCM approximation.
    q := matrix (phi | psi);
    r := p//q;
    r0 := id_F0//q;
    k := syz q;
    K := source k;
    G := coSyzygyChain(1, M');
    sour := F0 ++ K;
    tar := G_(-1);
    N := coker(G.dd_0*(r | k));
    map(N,M, G.dd_0*r0)
    )

///
restart
loadPackage("MCMApproximations", Reload =>true)
///

TEST///setRandomSeed 100
c = 3;d=3;
S = setupRings(c,d)
R = S_c
Mc = coker vars R
(M,k,p) = setupModules(S,Mc)
M_(c-1)
ca = coApproximation M_(c-1)
M'' = coker ca
N = target ca
assert(profondeur M'' == dim ring M'') -- an MCM module
assert(M'' == source approximation(M'', Total=>false)) -- no free summands
assert(2 == length res(N, LengthLimit =>10)) -- projective dimension <\infty
///

--<<docTemplate
doc ///
   Key
    coApproximation
    (coApproximation, Module)
    [coApproximation, CoDepth]
   Headline
    Maximal Cohen-Macaulay co-approximation of M
   Usage
    a = coApproximation M
   Inputs
    M:Module
   Outputs
    a:Matrix
   Description
    Text
     If R is a Gorenstein ring, and M is a finitely generated R-module, then, according
     to the theory of Auslander and Buchweitz (a good exposition is in Ding's Thesis) 
     there are unique exact sequences
     $$0\to K \to M' \to M\to 0$$
     and 
     $$0\to M \to N\to M''\to 0$$
     such that K and N are of finite projective dimension, M' and M'' are 
     maximal Cohen-Macaulay, and 
     M'' has no free summands. 
     The call
     
      approximation M  
      
      returns the map $M'\to M$, while the call
      
      coApproximation M
      
      returns the map $M\to N$.
      
      Since the script coApproximation begins by computing the approximation, it may
      shorten the computation if the user knows the depth of M in advance, specified
      with the option Depth => d.
    Example
     setRandomSeed 100
     c = 3;d=3;
     S = setupRings(c,d);
     R = S_c; -- complete intersection, codim = c
     R' = S_(c-1); --codim c-1
     Mc = coker vars R;
     (M,k,p) = setupModules(S,Mc); --M_(c-1) is Mc as an R_(c-1)-module
     ca = coApproximation M_(c-1); 
     M'' = coker ca;
     N = target ca
     profondeur M'' == dim ring M'' -- an MCM module
     M'' == source approximation(M'', Total=>false) -- no free summands
     2 == length res(N, LengthLimit =>10) -- projective dimension <\infty
   SeeAlso
    setupRings
    setupModules
    profondeur
    approximation
    syzygy
///


approximation = method(Options =>{CoDepth=>-1, Total =>true})
approximation Module := opts -> M->(
    --returns the list {phi, psi} where:
    --phi is the map from the essential MCM approximation
    --psi is the minimal map from a free module necessary to make
    -- alpha = (phi | psi) an epimorphism
    phi := approximatione(M,CoDepth=>opts.CoDepth);
    if opts.Total != true then return phi;
    psi := null;
    N := coker phi;
    N1 := prune N;
    if N1 == 0 then (
	psi = map(M,(ring M)^0, 0);
        return (phi, psi));
    MtoN := map(N,M, id_(cover M));
    a := N1.cache.pruningMap;
    psi = (matrix a)//matrix(MtoN);
    (phi, psi)
    )


doc ///
   Key
    Total
   Headline
    option for approximation
   Usage
    approximation(M, Total =>t)
   Inputs
    M:Module
    t:Boolean
   Description
    Text
     If t != true then return only the map from the non-free part of the MCM approximation
     Otherwise, return the pair of maps that defines the MCM approximation.
     Default is t ==true.
   SeeAlso
    approximation
    auslanderInvariant
    regularitySequence
    CoDepth
///



doc ///
   Key
    approx
   Headline
    synonym for approximation
   SeeAlso
    approximation
///

--approx := approximation
///
    phi = approximation(M, Total => false)
    (approximation, Module)
    [approximation, Total]
    [approximation, CoDepth]
///

///
restart
loadPackage("MCMApproximations", Reload =>true)
///

doc ///
   Key
    approximation
    (approximation, Module)
    [approximation, Total]
    [approximation, CoDepth]
   Headline
    returns pair of components of the map from the MCM approximation
   Usage
    (phi,psi) = approximation M
   Inputs
    M:Module
   Outputs
    phi:Matrix
     map from the nonfree component
    psi:Matrix
     map from the free component
   Description
    Text
     If R is a local or standard graded
     Gorenstein ring, and M is a finitely generated R-module, then, according
     to the theory of Auslander and Buchweitz (a good exposition is in Ding's Thesis) 
     there are unique exact sequences
     $$0\to K \to M' \to M\to 0$$
     and 
     $$0\to M \to N\to M''\to 0$$
     such that K and N are of finite projective dimension, M' and M'' are 
     maximal Cohen-Macaulay, and 
     M'' has no free summands. Thus, for example, the projective
     dimension of K is one less than the CoDepth of M.)
 
     The call
     
      coApproximation M  
      
      returns the map $M\to N$, while the call
      
      approximation M
      
      returns the pair (phi,psi), which define the map $M'\to M$.
      Here phi is the "essential MCM approximation" from the biggest summand M'0 of 
      M' that has no free summands, and psi is the map from the free summand M'1.
     
     The module M'0 is computed as syzygy(-k, syzygy(k,M)) for any k >= CoDepth M,
     and the map $M'0 \to M$ is induced by the comparison map of resolutions. 
     
     The rank t of the free summand M'1 is called the Auslander Invariant of M,
     and is returned by the call auslanderInvariant M.
     
     The CoDepth of M can be provided as an option to speed computation.
     
     If Total => false, then just the map phi is returned.
    Example
     R = ZZ/101[a,b]/ideal(a^2)
     k = coker vars R
     approximation k
     M = image vars R
     approximation M
     approximation(M, Total=>false)
     approximation(M, CoDepth => 0)
   SeeAlso
    syzygy
    auslanderInvariant
///

///TEST
setRandomSeed 100
assert( (approximation M) === (map(image map((R)^1,(R)^{{-1},{-1}},{{a, b}}),cokernel map((R)^{{-1},{-1}},(R)^{{-2},{-2}},{{-a, b}, {0, a}}),{{-1, 0}, {0, 1}}),map(image map((R)^1,(R)^{{-1},{-1}},{{a, b}}),(R)^0,0)) );
assert( (approximation(M, Total=>false)) === map(image map((R)^1,(R)^{{-1},{-1}},{{a,b}}),cokernel map((R)^{{-1},{-1}},(R)^{{-2},{-2}},{{-a, b}, {0, a}}),{{-1, 0}, {0, 1}}) );
assert( (approximation(M, CoDepth => 0)) === (map(image map((R)^1,(R)^{{-1},{-1}},{{a,b}}),cokernel map((R)^{{-1},{-1}},(R)^{{-2},{-2}},{{a, -b}, {0, a}}),{{1, 0}, {0,1}}),map(image map((R)^1,(R)^{{-1},{-1}},{{a, b}}),(R)^0,0)) );
///

auslanderInvariant = method(Options =>{CoDepth => -1})
auslanderInvariant Module := opts->M-> (
    --number of free summands in the MCM approximation
    phi := approximation(M, CoDepth => opts.CoDepth, Total=>false);
    numgens prune coker phi)
///
restart
loadPackage("MCMApproximations", Reload =>true)
     S = ZZ/101[a,b,c,d]
     N = matrix{{0,a,0,0,c},
	     	{0,0,b,c,0},
		{0,0,0,a,0},
		{0,0,0,0,b},
		{0,0,0,0,0}}
     M = N-transpose N
     J = pfaffians(4,M)
     R = S/J
     auslanderInvariant coker vars R
///

doc ///
   Key
    auslanderInvariant
    (auslanderInvariant, Module)
    [auslanderInvariant, CoDepth]
   Headline
    measures failure of surjectivity of the essential MCM approximation
   Usage
    a = auslanderInvariant M
   Inputs
    M:Module
   Outputs
    a:ZZ
   Description
    Text
     If R is a Gorenstein local ring and M is an R-module, then
     the essential MCM approximation is a map phi: M'-->M, where 
     M' is an MCM R-module, obtained as the k-th cosyzygy of the k-th syzygy of M,
     where k >= the co-depth of M. The Auslander invariant is the number of 
     generators of coker phi. Thus if R is regular the Auslander invariant is
     just the minimal number of generators of M, and if M is already an MCM module
     with no free summands then the Auslander invariant is 0.
     
     Ding showed that if R is a hypersurface ring, then
     auslanderInvariant (R^1)/((ideal vars R)^i) is zero precisely for i<multiplicty R.
     
     Experimentally, it looks as if for a complete intersection the power is the 
     a-invariant plus 1, but NOT for the codim 3 Pfaffian example.
    Example
     R = ZZ/101[a..d]/ideal"a3"
     apply(5, i -> auslanderInvariant ((R^1)/(ideal(vars R))^(i+1)))
     R = ZZ/101[a..d]/ideal"a3,b4"
     apply(6, i -> auslanderInvariant ((R^1)/(ideal(vars R))^(i+1)))
     S = ZZ/101[a,b,c]
     N = matrix{{0,a,0,0,c},
	     	{0,0,b,c,0},
		{0,0,0,a,0},
		{0,0,0,0,b},
		{0,0,0,0,0}}
     M = N-transpose N
     J = pfaffians(4,M)
     R = S/J
     I = ideal vars R
     scan(5, i->print auslanderInvariant ((R^1)/(I^i)))
   SeeAlso
    approximation
///


setupRings = method(Options =>{Characteristic => 101})
setupRings(ZZ,ZZ) := opts -> (c,d)->(
    x := local x;
    p := opts.Characteristic;
    S := ZZ/101[x_0..x_(c-1)];
    ff := matrix{apply(c, i->S_i^d)};
    ff = ff*random(source ff, source ff);
    {S}|apply(c, j->(S/ideal(ff_{0..j}))
	)
    )
--<<docTemplate
doc ///
   Key
    Characteristic
   Headline
    Option for setupRings(c,d,Characteristic=>q)
   Description
    Text
     Allows the user to specify the characteristic of the rings to be defined.
   SeeAlso
    setupRings
    setupModules
///

doc ///
   Key
    setupRings
    (setupRings, ZZ, ZZ)
    [setupRings, Characteristic]
   Headline
    Sets up a complete intersection for experiments
   Usage
    R = setupRings(c,d)
   Inputs
    c:ZZ
     desired codimension
    d:ZZ
     degree of homogoneous generators
   Outputs
    R:List
     List of rings R_0..R_c with R_i = S/(f_0..f_(i-1))
   Description
    Text
     Uses the complete intersection f_0..f_(c-1) to be random combinations of x_0^d..x_(c-1)^d
     in the polynomial ring ZZ/p[x_0..x_c], where p can be set by the optional 
     argument Characteristic=>p.
    Example
     netList setupRings(2,2)
     netList setupRings(2,2,Characteristic=>5)
   SeeAlso
    setupModules
///


setupModules = method()
setupModules(List,Module) := (R,M)->(
    --R_i is a ci of codim i in a ring S
    --returns (MM,kk,p) where
    --MM,kk are lists whose i-compoents are the module M and residue field k, but over R_i
    --p_i_j is the projection from R_j to R_i (c >= i >= j >= 0)
    c := length R-1;
    kk :=apply(c+1, i-> coker vars R_i);
    p := apply(c+1, i->apply(i+1, j->map(R_i,R_j)));
    MM := apply(c+1, j->prune pushForward(p_c_j, M));
    (MM,kk,p))
///
restart
loadPackage("MCMApproximations", Reload=>true)
///    

TEST///
setRandomSeed 100
c=3;d=2;
R = setupRings(c,d);
(M,k,p) = setupModules(R,coker vars R_c);
assert(numcols  matrix p_c_c === 3 )
///

doc ///
   Key
    setupModules
    (setupModules, List, Module)
   Headline
    Prepares modules over a complete intersection for experiment
   Usage
    (MM,kk,p) = setupModules(R,M)
   Inputs
    R:List
     list of rings R_0..R_c as produce by setupRings
    M:Module
     module over R_c
   Outputs
    MM:List
     MM_i is M as a module over R_i
    kk:List
     kk_i is the residule field of R_i, as a module
    p:List
     p is the list of lists of projection maps, p_i_j: R_j->R_i for 0<=j<=i<=c
   Description
    Text
     In the following examples, the syzygies all 
     have regularity evenExtModule MM_1 == 1
     because the complexity of M is only 2.
    Example
     needsPackage "CompleteIntersectionResolutions"
     c = 3
     R = setupRings(3,c);
     Rc = R_c;
     M = coker matrix{{Rc_0,Rc_1,Rc_2},{Rc_1,Rc_2,Rc_0}}
     (MM,kk,p) = setupModules(R,syzygy_3 M);
     regularity evenExtModule MM_3
     regularity evenExtModule MM_1     
   SeeAlso
    setupRings
///

{*
projection = (R,i,j) -> (
    --Assumes that R is a list of rings, and that R_(i+1) is a quotient of R_i
    --forms the projection maps 
    --NOTE R_i = R(i+1) in our usual notation!
    --projection(R,i,j) is R(j) --> R(i).
    c := length R;
    if i>j then error "need first index <= second";
    if i<0 or j>c then error "indices between 0 and c";
    if i == 0 then map(R_(j-1),ambient R_0) else
    map(R_(j-1), R_(i-1))
    )
*}
regularitySequence = method()
regularitySequence(List, Module) := (R,M) ->(
    --R = complete intersection list R_(i+1) = R_i/f_(i+1), i= 0..c.
    --M = module over R_c
    --returns the list of pairs {reg evenExtModule M_i, reg oddExtModule M_i}
    --where M_i is the MCM approximation of M over R_i
    em := null;
    om := null;
    c := length R-1;
    (MList,kkk,p) := setupModules(R,M);
    MM := apply(c+1, j->source approximation(pushForward(p_c_j, M),Total =>false));
    MM = select(MM, m-> not isFreeModule m);
    <<"reg even ext, soc degs even ext, reg odd ext, soc degs odd ext"<<endl<<endl;
    scan(reverse MM, m-> (
	    em = evenExtModule m;
	    om = oddExtModule m;
     <<{regularity em, socleDegrees em, regularity om, socleDegrees om})
     <<endl);
    )


///
restart
loadPackage("MCMApproximations", Reload=>true)
///
TEST///
setRandomSeed 100
c = 2
d = 2
R = setupRings(c,d)
(M,k,p) = setupModules(R,coker vars R_c);
regularitySequence(R,coker vars R_c)
///


beginDocumentation()

doc ///
   Key
    regularitySequence
    (regularitySequence, List,Module)
   Headline
    regularity of Ext modules for a sequence of MCM approximations
   Usage
    L = regularitySequence (R,M)

   Inputs
    R:List
     list of rings R_i = S/(f_0..f_(i-1), complete intersections
    M:Module
     module over R_c where c = length R - 1.
   Outputs
    L:List
     List of pairs {regularity evenExtModule M_i, regularity oddExtModule M_i)
   Description
    Text
     Computes the non-free parts M_i of the MCM approximation to M over R_i, 
     stopping when M_i becomes free, and
     returns the list whose elements are the pairs of regularities, starting
     with M_(c-1)
     Note that the first pair is for the 
    Example
     c = 3;d=2
     R = setupRings(c,d);
     Rc = R_c
     M = coker matrix{{Rc_0,Rc_1,Rc_2},{Rc_1,Rc_2,Rc_0}}
     regularitySequence(R,M)
   SeeAlso
    approximation
    auslanderInvariant
///

doc ///
Key
  MCMApproximations
Headline
  Maximal Cohen-Macaulay Approximations and Complete Intersections
Description
  Text
  Example
Caveat
SeeAlso
///
{*
doc ///
Key
  Headline
Usage
Inputs
Outputs
Consequences
Description
  Text
  Example
  Code
  Pre
Caveat
SeeAlso
///
*}
TEST ///
-- test code and assertions here
-- may have as many TEST sections as needed
///
///
restart
loadPackage( "MCMApproximations", Reload=>true)
///

TEST///
kk = ZZ/101
R = kk[x,y,z]
assert(3==profondeur R)
assert (2 == profondeur(ideal(x,y), R^1))
assert(0 == profondeur coker vars R)
assert (0 == profondeur(ideal(x,y), coker vars R))
R = ZZ/101[a..f]
I = minors(2,genericSymmetricMatrix(R,a,3))
assert (profondeur(R/I) ==3)
assert(profondeur(R/I^2) == 0)
mm = ideal vars (R/I)
assert(profondeur(mm, (R/I)^1)== 3)
///
TEST///
S = ZZ/101[a,b,c]
R = S/ideal"a3,b3,c3"
use S
R' = S/ideal"a3,b3"
M = coker vars R
assert( (pushForward(map(R,R'),M)) === cokernel map((R')^1,(R')^{{-1},{-1},{-1}},{{c, b, a}}) );
use S
assert( (pushForward(map(R,S), M)) === cokernel map((S)^1,(S)^{{-1},{-1},{-1}},{{c, b, a}}) );
///
TEST///
setRandomSeed()
c = 3
R = setupRings(c,3)
M = syzygy(1,coker vars R_c)
(MM,kk,p) = setupModules(R,M);
auslanderInvariant syzygy_2 MM_1
assert (1 ==auslanderInvariant syzygy_2 MM_1)
(0 ==auslanderInvariant kk_2)
assert(p_1_0 === map(R_1,R_0))
///


///
restart
load"MCMApproximations.m2"
///
TEST///
setRandomSeed()
S = ZZ/101[a,b,c]
R = S/ideal"a3,b3,c3"
use S
R' = S/ideal"a3,b3"
M = coker vars R
(phi,psi) = approximation(pushForward(map(R,R'),ker syz presentation M))
assert( (prune source phi) === cokernel map((R')^{{-4},{-4},{-4},{-4},{-4},{-4},{-3}},(R')^{{-5},{-5},{-5},{-5},{-5},{-5},{-6},{-6},{-6}},
	      {{c,-b, 0, 0, 0, 0, a^2, 0, 0}, {0, 0, b, 0, -c, 0, 0, a^2, 0}, {a, 0, 0, 0, 0, -b, 0, 0, 0}, 
		  {0, a, 0, 0,0, -c, 0, -b^2, 0}, {0, 0, a, c, 0, 0, 0, 0, b^2}, {0, 0, 0, b, a, 0, 0, 0, 0}, {0, 0, 0, 0, b^2, a^2, 0, 0, 0}}) )
assert( (prune source psi) === (R')^{{-4},{-4},{-4}} )
assert(isSurjective(phi|psi)===true)
assert( (prune ker (phi|psi)) === (R')^{{-5},{-5},{-5},{-6},{-6},{-6}} );
///

test = method()
test(List,Module,ZZ,ZZ) := (S,Mc, low, high) ->(
c := length S -1;
R' := S_(c-1);
R := S_c;
RR' := map(R,R');
ff := presentation R;
K := coefficientRing R;
KR := map(K,R);
(M,kk,p) := setupModules(S,Mc);
<< regularitySequence(S,Mc)<<endl;
T := TateResolution(Mc,low,high);
tt := apply(toList(low+2..high), i-> makeT(ff, T, i));
phi' := apply(toList(low+1..high), --was high-2
    j->approximation(pushForward(RR', coker T.dd_j), Total => false));
phi := phi'/(ph ->  prune map(R**target ph, R**source ph, RR' matrix ph));
report := matrix{toList(low+2..high), 
       apply(toList(low+2..high), i->if isSurjective tt_i_(c-1) then 0 else 1),
       apply(toList(low+2..high), i->(numgens ker KR matrix phi_(i+low-1))),
       apply(toList(low+2..high), i->(regularity evenExtModule coker T.dd_i))};
<<"KEY:"<<endl;
<<"report_(0,j) = i : index of a free module F_i in T"<<endl;
<<"report_(1,j): whether the CI map emerging from F_i is surjective"<<endl;
<<"report_(2,j): whether the CM approx embeds mod the max ideal"<<endl;
<<"report_(3,j): regularity of the even ext module"<<endl;
report)

--<<docTemplate
doc ///
   Key
    test
    (test, List, Module, ZZ, ZZ)
   Headline
    reports on factors related to the one-step resolution
   Usage
    report = test(S, Mc, low, high)
   Inputs
    S:List
     list of successive rings S_0, S_0/(f_1) .. S_c = S_0/(f_1..f_c)
    Mc:Module
     module over S_c
    low:ZZ
     start of window of Tate resolution
    high:ZZ
     end of window of Tate resoluion
    report:Matrix
     matrix of integers:
   Description
    Text
     "report_(0,j) = i : index of a free module F_i in T"
     "report_(1,j): whether the CI map emerging from F_i is surjective"
     "report_(2,j): whether the CM approx embeds mod the max ideal"
     "report_(3,j): regularity of the even ext module"
    Example
      low = -2; high = 4;
      c = 2; d=3;
      S = setupRings(c,d);
      R = S_c;
      Mc = coker random(R^1, R^{2:-2})
      Mc = coker random(R^2, R^{-2,-3})
      time test(S,Mc,low,high)
   SeeAlso
    regularitySequence
    socleDegrees
///

end--
restart
uninstallPackage("CompleteIntersectionResolutions2")
installPackage("CompleteIntersectionResolutions2")
check "CompleteIntersectionResolutions2"

uninstallPackage"MCMApproximations"
installPackage"MCMApproximations"
check "MCMApproximations"
viewHelp MCMApproximations
--installPackage ("CompleteIntersectionResolutions")
-----Where does "high syzygy" behavior begin?
--Conjecture: where regularity of the even and odd ext modules is 0 -- independently of whether there are socle elements in degree 0.
--but to produce the behavior, the CM approx method is necessary; our matrixFactorization script won't do it!
--need to test this conjecture further!


--First of all, both the even and odd regularities seem to
--be inherited by the MCM approx module.

--In the case of one of the syzygies of the res field in c=3,
--it seems that reg evenExtModule = 1, reg oddExtModule =0 is enough!!
--In case c= 4 even {2,1} seems to be good enough. Note that's a case where
--reg ExtModule = 4.

--One-step conjecture: if R is codim 1 in R', complete intersections in S,
--and  M is a CM module over R, then:
--the resoluttion of the "R'-CM-approx map" over S is equal to the 
--resolution of M over S 
--iff
--Ext_R(M,k) has trivial summands in degrees 0,1 and after factoring those out
--the CI operator is a nzd.
--Moreover, In this case, the Ext module of the essential R' CM approximation
--is (Ext_R(M,k)/socle)/t

--If this is true, then in the case when Ext_R(M,k) has regularity <= 1 AND if the reg Ext_R'(M',k) <= reg Ext_R(M,k), thi could continue
--inductively. Note that reg(E/tE) <= reg(E) if t is a quasi-regular element on E (that is: a nzd on E/H^0_mm(E)). On the other hand,
-- Ext_R'(M',k) ! =  Ext_R(M,k)/t, so we can't use this directly.

--A crucial question is whether the socle of Ext_R(M,k) is represented by a free summand of the resolution.

----------------- Where regularity and minimality criteria set in
---we should add a test for the presence of socle in Ext^0.
restart
loadPackage("MCMApproximations", Reload=>true)
low = -2
high = 4
c = 2; d=3;
S = setupRings(c,d);
R = S_c;
--Mc = coker matrix {{R_0,R_1,R_2},{R_1,R_2,R_0}} -- with 3 vars
-- Mc = coker matrix {{R_0,R_1,R_2},{R_1,R_2,R_3}} -- with 4 vars this is too slow
Mc = coker random(R^1, R^{2:-2})
Mc = coker random(R^2, R^{-2,-3})
time test(S,Mc,low,high)

--installPackage "MCMApproximations"
--installPackage "CompleteIntersectionResolutions2"



--Conjecture 1: the "regularity of the successive MCM approximations is decreasing
restart
installPackage "MCMApproximations"
loadPackage("MCMApproximations", Reload=>true)
c = 3
R =setupRings(c,3)
Rc=R_c
M0 = coker vars Rc
range  = toList(-2..3)

scan(range, i-> (
	MM0 = syzygy(i,M0);
	Ee := null; Eo:= null;
	(M,kkk,p) = setupModules(R,MM0);
	apply(c-1, j->(
	a := auslanderInvariant M_(c-1-j);
	phi = approximation(M_(c-1-j),Total=>false);
	b := numgens prune ker(kkk_(c-1-j)**phi);
	re := regularity (Ee = evenExtModule(M_(c-1-j)));
	ro := regularity (Eo = oddExtModule(M_(c-1-j)));	
	se := degree Hom(coker vars ring Ee, Ee);
	so := degree Hom(coker vars ring Eo, Eo);	
	<<{{i,c-1-j},{a,b},{re,se}, {ro, so}};<<endl;<<endl;
	flush;
	))
    ))



------image of essential approximation, compared with ker t.
restart
loadPackage("MCMApproximations", Reload=>true)
loadPackage("CompleteIntersectionResolutions2", Reload=>true)

tensor (Ring,Matrix) := (R,phi) -> (
    RR' := map(R, ring phi);
    map(R**target phi, R**source phi, RR' matrix phi)
    )

--the following uses notation from "test";
--should also test whether the kernel of t is the image of phi all mod the max ideal.

L0 = apply(toList(low..high+low-1),i->(
	m1 := map(coker T.dd_(i+1), coker T.dd_(i+3), tt_(i+low)_2);
	m2 := phi_(i+2+low);
	{m1,m2}));

L1 = apply(toList(low..high+low-1),i->(
	m1 := tt_(i-low)_2;
	m2 := matrix phi_(i+2-low);
	{m1,m2}));

matrix{toList(low..high+low-1),
        apply(L1, p ->if KR(map(target p_0, source p_1, matrix p_0 * matrix p_1))!=0 then 1 else 0)}


L2 = apply(toList(low..high+low-1),i->(

	m1 := map(coker T.dd_(i+1), coker T.dd_(i+3), tt_(i-low)_2);
	m2 := phi_(i+2-low);
	--why can't we write m1*m2? the target of m2 is supposedly the same as the source of m1!
	map(target m1, source m2, matrix (m1) * matrix(m2))));

L3 = apply(toList(low..high+low-1),i->(
	m1 := tt_(i-low)_2;
	m2 := matrix phi_(i+2-low);
	{m1,m2};
	m1*m2))

