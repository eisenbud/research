-- /Applications/Macaulay2-1.12/share/Macaulay2/Core/ext.m2:89:39-179:3: --source code:
needsPackage "CompleteIntersectionResolutions"

Ext1 = method()
Ext1(Module) := Module => (M) -> (
       N  := coker vars ring M;
       cacheModule := M; -- we have no way to tell whether N is younger than M, sigh
       cacheKey := (Ext,M,N);
       if cacheModule.cache#?cacheKey then return cacheModule.cache#cacheKey;
       B := ring M;
       if B =!= ring N
       then error "expected modules over the same ring";
       if not isCommutative B
       then error "'Ext' not implemented yet for noncommutative rings.";
       if not isHomogeneous B
       then error "'Ext' received modules over an inhomogeneous ring";
       if not isHomogeneous N or not isHomogeneous M
       then error "'Ext' received an inhomogeneous module";
       if N == 0 or M == 0 then return cacheModule.cache#cacheKey = B^0;

       p := presentation B;
       A := ring p;
       I := ideal mingens ideal p;
       n := numgens A;
       c := numgens I;
       if c =!= codim B 
       then error "total Ext available only for complete intersections";

       f := apply(c, i -> I_i);
       pM := lift(presentation M,A);
       pN := lift(presentation N,A);
       M' := cokernel ( pM | p ** id_(target pM) );
       N' := cokernel ( pN | p ** id_(target pN) );
       assert isHomogeneous M';
       assert isHomogeneous N';

--work begins here

       C := complete resolution M';

       X := getSymbol "X";
       K := coefficientRing A;
       S := K(monoid [X_1 .. X_c, toSequence A.generatorSymbols,
         Degrees => {
           apply(0 .. c-1, i -> prepend(-2, - degree f_i)),
           apply(0 .. n-1, j -> prepend( 0,   degree A_j))
           }]);
error();
       -- make a monoid whose monomials can be used as indices
       Rmon := monoid [X_1 .. X_c,Degrees=>{c:{2}}];
       -- make group ring, so 'basis' can enumerate the monomials
       R := K Rmon;

       -- make a hash table to store the blocks of the matrix
       blks := new MutableHashTable;
       blks#(exponents 1_Rmon) = C.dd;
       scan(0 .. c-1, i -> 
            blks#(exponents Rmon_i) = nullhomotopy (- f_i*id_C));
--
       -- a helper function to list the factorizations of a monomial
       factorizations := (gamma) -> (
         -- Input: gamma is the list of exponents for a monomial
         -- Return a list of pairs of lists of exponents showing the
         -- possible factorizations of gamma.
         if gamma === {} then { ({}, {}) }
         else (
           i := gamma#-1;
           splice apply(factorizations drop(gamma,-1), 
             (alpha,beta) -> apply (0..i, 
                  j -> (append(alpha,j), append(beta,i-j))))));
  --
       scan(4 .. length C + 1, 
         d -> if even d then (
           scan( flatten \ exponents \ leadMonomial \ first entries basis(d,R), 
             gamma -> (
               s := - sum(factorizations gamma,
                 (alpha,beta) -> (
                   if blks#?alpha and blks#?beta
                   then blks#alpha * blks#beta
                   else 0));
               -- compute and save the nonzero nullhomotopies
               if s != 0 then blks#gamma = nullhomotopy s;
               ))));
       -- make a free module whose basis elements have the right degrees
       spots := C -> sort select(keys C, i -> class i === ZZ);
       Cstar := S^(apply(spots C,
           i -> toSequence apply(degrees C_i, d -> prepend(i,d))));

       -- assemble the matrix from its blocks.
       -- We omit the sign (-1)^(n+1) which would ordinarily be used,
       -- which does not affect the homology.
       toS := map(S,A,apply(toList(c .. c+n-1), i -> S_i),
         DegreeMap => prepend_0);
       Delta := map(Cstar, Cstar, 
         transpose sum(keys blks, m -> S_m * toS sum blks#m),
         Degree => { -1, degreeLength A:0 });
       DeltaBar := Delta ** (toS ** N');
       if debugLevel > 10 then (
            assert isHomogeneous DeltaBar;
            assert(DeltaBar * DeltaBar == 0);
            stderr << describe ring DeltaBar <<endl;
            stderr << toExternalString DeltaBar << endl;
            );

       -- now compute the total Ext as a single homology module
       tot := minimalPresentation homology(DeltaBar,DeltaBar);
       cacheModule.cache#cacheKey = tot;
       tot)
-*
ExtByShamash = method()
ExtByShamash(Matrix, Module, ZZ) := (Q,M,d) -> (
    --Q 1xc matrix, a complete intersection in S = ring M
    --M an S-module annihilated by Q
    --forms the Hom of the Shamash resolution to the residue field up to degree d.
    S := ring M;
    kk := coefficientRing S;
    c := numcols Q;
    T := kk[t_0..t_(c-1)];
        
    F := complete res M;
    F' = dual F;
    H := makeHomotopies(Q,F);
*-  

eps = M -> inducedMap(M,target presentation M)
    
ExtCover = method()
ExtCover(ZZ,ChainComplex, Module) := (d,F,N) ->(
    --returns a map E -> Hom (F_d,N) from a free module E to a set of elements that
    --generate Ext^d(M,N)
    --so that homomorphism(E_{i}) is the corresponding map F_d ->N.
K := ker Hom (F.dd_(d+1), M);
B := image Hom (F.dd_(d), M);
(eps(K/B)//inducedMap(K/B,K)))

ExtCover(ZZ,Module,Module) := (d,M,N) -> 
    ExtCover(d,res(M, LengthLimit => d+1),N)
            
comp = method()
comp(List, ChainComplex, ChainComplex, Module) :=  (L,F,G,P) ->(
    --If L = {p,q},
    --and F is a resolution of M of length at least p+q+1, 
    --and G is a resolution of N of length at least q+1,
    --return a map e: where e(i,j) is the element of ExtCover(M,P)
    --resulting from the composition of Ext^d(M,N)**Ext^e(N,P) --> Ext^d+e(M,P)
    p := L_0; 
    q := L_1;
    N := coker G.dd_1;
    epN := inducedMap(N,G_0);
    EMN := ExtCover(p,F,N);    
    (i,j) -> (
	EMN := ExtCover(p,F,N);
	phi' := homomorphism(EMN_{i}); -- map from F_1 to N
	phi := phi'//inducedMap(N,G_0);
	F' := F[p];
	phiq := (extend(G,F',phi))_q;
	ENP := ExtCover(q,G,P);
	psi := homomorphism(ENP_{j});
	psi*phiq)
    )

comp(List, Module, Module, Module) :=  (L,M,N,P) ->(
    --If F is a resolution of M of length at least p+q+1, 
    --and L = {p,q}, then
    --return a map e: where e(i,j) is the element of ExtCover(M,P)
    --resulting from the composition of Ext^d(M,N)**Ext^e(N,P) --> Ext^d+e(M,P)
    F := res(M, LengthLimit => 1+sum L);
    G := res (N, LengthLimit => 1+L_1);
    comp(L,F,G,P))

toCIOperators = method()
toCIOperators (Matrix,List, ChainComplex,ZZ) := (Q,L,F,i)-> (
    --Q is a 1 x c matrix containing entries that annihilate a 
    --module M
    --L is a list of polynomials of a single degree d
    --in auxilliary variables t_i
    --corresponding to the entries of Q
    --F is a resolution of M of length at least 
    -- i+2*d
    --Output is a list of maps  F_(i+2d) --> F_i
    d = (degree L_0)_0; -- the common degree
    tt = apply(d, j-> makeT(Q,F,i-2*j));
    C = coefficients L_0;
    mm = apply(numcols(C_0), u->C_0_u_0); -- the  monomials in L_0
    ee = apply(#mm, u-> flatten exponents (mm_u));
    pp = apply(#ee, j->flatten apply (
	        #(ee_j), 
		s-> apply(ee_j_s, k->tt_s_s))
	       );
sum(apply(#pp, u -> product reverse (pp_u)))
)
///
restart
debug needsPackage "CompleteIntersectionResolutions"
load "ExtStructure.m2"
kk = ZZ/101
S = kk[x_0..x_3]
Q = matrix{{3*x_0*x_1-7*x_2*x_3, x_0*x_2-x_1*x_3}}
R = S/ideal Q
F = res coker vars R
T = kk[t_1,t_2]
U = flatten entries gens (ideal vars T)^2
m = U_0
n = U_1
a = m+5*n
L = {n}
toCIOperators(Q,L,F,5)
///
end--
restart
debug needsPackage "CompleteIntersectionResolutions"
--viewHelp CompleteIntersectionResolutions
--viewHelp makeT
load "ExtStructure.m2"
kk = ZZ/101
S = kk[x_0..x_3]
Q = matrix{{3*x_0*x_1-7*x_2*x_3, x_0*x_2-x_1*x_3}}
f = x_0^2+3*x_1^2+5*x_2^2+7*x_3^2
R = S/ideal f
M = coker vars R
F = res(M, LengthLimit =>5)
c1 = comp({2,2},M,M,M)
c = comp({2,2},F,F,M)
N1 = netList flatten apply(4, i-> apply(4, j->{i,j,c1(i,j)}))
N2 = netList flatten apply(4, i-> apply(4, j->{i,j,c(i,j)}))
N1 == N2





    


    





