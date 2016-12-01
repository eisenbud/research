newPackage(
	"NodalCurves",
    	Version => "0.3", 
    	Date => "March 15, 2012",
    	Authors => {{Name => "Frank-Olaf Schreyer", 
		  Email => "schreyer@math.uni-sb.de", 
		  HomePage => "http://www.math.uni-sb.de/ag/schreyer/"}
                   },
    	Headline => "Construction of random nodal rational curves",
    	DebuggingMode => true
        )


export{canonicalMultipliers,
     linearSeriesFromMultipliers,
     changeMultiplier,
     distinctPointsOfP1,
     randomPrymCanonicalNodalCurve,
     randomCanonicalNodalCurve,
     Printing,
     Timings,
     syzygiesOfPrymCanonicalNodalCurve,
     syzygiesOfTorsionBundle,
     criticalBettiNumber,
     verifyConjA,
     verifyConjB}

needsPackage("extrasForTheKernel")

setRandomSeed("hope this starting point works")

distinctPointsOfP1=method()
     distinctPointsOfP1(Matrix) := P-> (
	  -- the 2xn matrix P with entries in the ground field K
	  -- represents n distinct points of P^1(K) if and only if
	  -- all 2x2 minors of P are nonzero
	  P2:=exteriorPower(2,P);
	  #select(toList(0..rank source P2-1),i-> P2_(0,i)==0)==0)

undocumented distinctPointsOfP1
canonicalMultipliers=method()

canonicalMultipliers(Matrix,Matrix) := (P,Q) -> (
     -- P and  Q two 2xg matrices representing 2g distinct points of P^1
     S:=ring P;
     if dim S != 2 then error "not a Polynomialring in two variables";
     g:= numcols P; 
     quadrics := apply(g, i->(det(P_{i}|(transpose vars S)))*(det(Q_{i}|(transpose vars S))));
     -- the quadrics with zero locus P_{i} and Q_{i}
     sections := (apply(g, i -> product(g, j-> if i == j then 1_S else quadrics_j)));
     -- a basis of the canonical series as subseries of S_{2g-2} of the nodal curve
     A := transpose matrix(apply(g, i ->{sub(sections_i, transpose P_{i}), sub(sections_i, transpose Q_{i})}));
     A)

linearSeriesFromMultipliers=method()

linearSeriesFromMultipliers(Sequence,Matrix) := (PQ,A) ->(
     -- PQ a list of two 2xg matrices representing distinct points of P^1
     -- A a 2xg matrix of ratios of identifying O_{P^1}(2g-2) tensor k(P_i) with O_{P^1}(2g-2) tensor k(Q_i)
     -- the result is the matrix of sections of O(2g-2) which obey these sections
     P:=PQ_0; Q:=PQ_1; 
     S := ring P;
     g := numcols P; 
     Bs := basis(2*g-2, S);
     MP := matrix(apply(numcols P, i->flatten entries(A_(1,i)*(sub(Bs, transpose P_{i})))));
     MQ := matrix(apply(numcols P, i->flatten entries(A_(0,i)*(sub(Bs, transpose Q_{i})))));
     sy := syz(MP-MQ);
     ell:= rank source sy;
     map(S^1, S^{ell:-2*g+2}, Bs*sy)
     )
undocumented linearSeriesFromMultipliers
TEST ///
S=ZZ/10007[x_0,x_1]
setRandomSeed("ok")
g=8
(P,Q)=(random(S^2,S^g),random(S^2,S^g))
assert(distinctPointsOfP1(P|Q))
A=canonicalMultipliers(P,Q)
s=linearSeriesFromMultipliers((p,Q),A)
assert(rank source s == g)
///
 


changeMultiplier=method()

changeMultiplier(Matrix,ZZ) := (A,r) -> (
     	  -- change all multpliers by a factor r
	  -- in applications r is often a root of unity
	  matrix apply(2,i->apply(rank source A,j-> if i==0 then A_(i,j) else r*A_(i,j))))

changeMultiplier(Matrix,ZZ,ZZ) := (A,r,k) -> (
          -- change k of the multpliers by a factor r
	  -- in applications r is often a root of unity
	  matrix apply(2,i->apply(rank source A,j-> 
		    if i==1 and j<k then r* A_(i,j) else A_(i,j)))
	  )     

undocumented changeMultiplier

randomCanonicalNodalCurve=method()
randomCanonicalNodalCurve(ZZ) := (g)->(
     isPrime(32003);
     kk:=ZZ/32003;
     x:=symbol x;
     S:=kk[x_0,x_1];
     PQ:=(random(S^2,S^g),random(S^2,S^g)); -- 2g points on P^1
     while not distinctPointsOfP1(PQ_0|PQ_1) do PQ=(random(S^2,S^g),random(S^2,S^g));
     A:=canonicalMultipliers(PQ);
     s:=linearSeriesFromMultipliers(PQ,A);
     assert(rank source s==g); 
     t:= symbol t;
     T:=kk[t_0..t_(rank source s - 1)];
     betti(I:=ideal mingens ker map(S,T,s));
     assert (degree I==2*g-2 and genus(T/I)==g);
     L:=(kk,S,PQ,A,s,T);
     (L,I))
     


randomPrymCanonicalNodalCurve=method()

randomPrymCanonicalNodalCurve(ZZ,ZZ,ZZ) := (g,n,k)->(
     (p,r):=getRootOfUnity(n,random(200));     
     kk:=ZZ/p;
     x:=symbol x;
     S:=kk[x_0,x_1];
     PQ:=(random(S^2,S^g),random(S^2,S^g));
     while not distinctPointsOfP1(PQ_0|PQ_1) do PQ=(random(S^2,S^g),random(S^2,S^g));
     A:=canonicalMultipliers(PQ);
     A=changeMultiplier(A,r,k);
     s:=linearSeriesFromMultipliers((PQ),A);
     assert(rank source s==g-1);
     t:=symbol t; 
     T:=kk[t_0..t_(rank source s - 1)];
     betti(I:=ideal mingens ker map(S,T,s));
     assert (degree I==2*g-2 and genus(T/I)==g);
     L:=(r,p,kk,S,PQ,A,s,T);
     (L,I))

randomPrymCanonicalNodalCurve(ZZ,ZZ) := 
     (g,n) -> randomPrymCanonicalNodalCurve(g,n,g)


TEST ///
     g=8,n=4
     (L,I)=randomPrymCanonicalNodalCurve(g,n);
     (r,p,kk,S,PO,A,s,T)=L;
     assert (degree I==2*g-2 and numgens T == g-1 and genus(T/I)==g)    
///




syzygiesOfPrymCanonicalNodalCurve=method(TypicalValue=>ChainComplex,Options=>{Printing=>false})    

syzygiesOfPrymCanonicalNodalCurve(ZZ,ZZ) := opt-> (g,n) -> (
     (L,I):=randomPrymCanonicalNodalCurve(g,n,g);
     (r,p,kk,S,PQ,A,s,T):=L;
     if opt.Printing then (print "expected syzygies:";
	  print expectedSyzygies(g-3,{1,g-3,g}));
     fI:=res(I,DegreeLimit=>1);
     if opt.Printing then ( print "first strand in the example"; print betti fI);
     fI)


syzygiesOfTorsionBundle = method(TypicalValue=>ChainComplex,Options=>{Printing=>false})

syzygiesOfTorsionBundle(ZZ,ZZ,ZZ):=opt->(g,n,k) ->(
     (L,I):=randomPrymCanonicalNodalCurve(g,n,g);
     (r,p,kk,S,PQ,A,s,T):=L;
     if opt.Printing then ( print "naively expected syzygies:";
	  print expectedSyzygies(g-3,{g-1,g-1}));      
     B:=changeMultiplier(A,r^(k-1),g);
     sA:=linearSeriesFromMultipliers(PQ,A);
     sB:=linearSeriesFromMultipliers(PQ,B);
     b1:=(g-1)^2-3*g+3;
     betti( m:=(syz flatten (transpose sB*sA)));
     m1:=m_{0..(b1-1)};
     ss:=symbol ss;
     TS:=T[ss_0..ss_(g-2)];	
     m2:=flatten(transpose vars TS*sub(vars T,TS))*sub(m1,TS);
     m3:=substitute(diff(transpose vars TS,m2),T);
     M3:=coker map(T^(g-1),T^{b1:-1},m3);
     fM3:=res(M3,DegreeLimit=>0);
     if opt.Printing then (print "linear strand in the example:";
	  print betti fM3);
     fM3)


criticalBettiNumber=method(Options=>{Printing=>false}) 
 
criticalBettiNumber(ZZ,ZZ):= opt-> (g,n) -> (
     k:=lift(g/2,ZZ);
     if opt.Printing then print expectedSyzygies(g-3,{g,g-3,1});
     (L,I):=randomPrymCanonicalNodalCurve(g,n);
     (r,p,kk,S,PQ,A,s,T):=L;
     B:=canonicalMultipliers(PQ_0,PQ_1);
     J:=ideal (s_{g-3,g-2});
     assert (dim J == 0);
     omega:=linearSeriesFromMultipliers(PQ,B);
     J2:=ideal omega *J;
     t:=symbol t;
     Tart:=kk[t_0..t_(g-4)];
     sart:=mingens ideal(s%J);
     kd:=koszul(k,vars Tart)**Tart^{1};
     kdS:=map(S^(rank target kd),S^{rank source kd:-2*g+2},sub(kd,sart));
     F:=omega**kdS;
     Sart:=S/J2;     
     Fart:=sub(F,Sart);
     F=lift(Fart,S);
     F)

TEST ///
    g=8,n=2;
time betti(F=criticalBettiNumber(g,n)) 
time betti syz(F,DegreeLimit=>(4*g-4))
///


verifyConjA=method(Options=>{Timings=>false,Printing=>false})
     
verifyConjA(ZZ,ZZ) := opt->(g,n) -> (
     F:=0;
     if opt.Timings then  time F=criticalBettiNumber(g,n,Printing=>opt.Printing) else F=criticalBettiNumber(g,n,Printing=>opt.Printing); 
     a:=rank source F;
     entriesF:=unique flatten entries F_{0};
     for i from 1 to a-1 do entriesF = unique((unique flatten entries F_{i})|entriesF); 
     lTerms:=leadTerm mingens ideal entriesF;
     kk:= coefficientRing ring lTerms;
     M:=0;sM:=0;
     if opt.Timings then time M=sub(contract(transpose lTerms, F),kk) else M=sub(contract(transpose lTerms, F),kk);
     if opt.Timings then time sM=syz M else sM=syz M;
     if opt.Printing then print (betti M,betti sM);     
     rank source sM ==0)
TEST ///
assert verifyConjA(8,3,Timings=>true,Printing=>true)
assert (verifyConjA(8,2,Timings=>true,Printing=>true) ==false)    
///

verifyConjB=method(Options=>{Printing=>false,Timings=>false})

verifyConjB(ZZ,ZZ,ZZ) := opt-> (g,n,k) -> (
     if g%2 ==1 then error "expected even genus";
     m:=lift(g/2,ZZ)-1;
     expectedRank:= if g%4==2 and n==2*k-1 and binomial(g-3,m)%2==1 then 1 else 0;
     F:=0;
     if opt.Timings then time F=syzygiesOfTorsionBundle(g,n,k,Printing=>opt.Printing) 
                    else F=syzygiesOfTorsionBundle(g,n,k,Printing=>opt.Printing);
     rank (F_m) == expectedRank
     )
TEST ///
     (g,n,k)=(6,5,3) 
     assert verifyConjB(6,5,3)
///

beginDocumentation()

doc ///
  Key
    NodalCurves
  Headline
    construction of nodal rational curves     
  Description
    Text
      {\bf What's new:}

      {\it Version 0.3:}      
       First version

      {\bf Overview:}
         Starting from a collection of g pairs of points
         P_i, Q_i the canonical  image of the rational curves with nodes at
         these points is constructed. Similarly, embedding of these curves 
         by the linear series $K \otimes L$ with $L$ an n-torsion bundle is constructed.
	 
         One main goal is to verify two conjectures. Conjecture A is the Prym-Green Conjecture on syzygies of 
	 Prym canonical curves of even genus g and level n, see @ HREF("http://arxiv.org/abs/0804.4616", "Farkas, Ludwig [2008]") @  
	 for small values of g and level n. This works up to genus 16 with the exception of genus (g,n)=(8,2) or (16,2). 
	 The case of genus 16 requires a lot of time and memory.
	 
	 Conjecture B concerns syzygies of torsion bundles $L^k$ in Prym canonical space $P(H^0(C,K\otimes L)$ again of even genus.
	 
     
      
      

      {\bf Setup:}

      This package requires Macaulay2 version 1.4 or newer.

      Install this @TO Package@ by doing

      @TO installPackage@("NodalCurves")

      {\bf Examples:}
///
doc ///
  Key 
    randomCanonicalNodalCurve
    (randomCanonicalNodalCurve,ZZ) 
  Headline 
    get a random canonical nodal curve of genus g 
  Usage
    (L,I)=randomCanonicalNodalCurve(g)
  Inputs
    g: ZZ
       the desired arithmetic genus
  Outputs
    L: Sequence
       of additionally created objects (kk,S,PQ,A,s,T) with
        kk = the ground field, 
	S = homogeneous coordinate ring of P^1, PQ a list of coordinate matrices P,Q
	of the preimages of the double points, A the canonical multipliers,
	s = the canonical system, and T the coordinate ring of P^{g-1}
    I: Ideal
       the ideal of the canonical rational curve 
  
  Description
     Text
       Construct a canonical rational curve with g double points.
       
       Step 1. Choose the prime p=32003.
       We then work over kk=ZZ/p and S=kk[x_0,x_1]. 
       
       Step 2.  Choose 2 times g points P_i,Q_i randomly in PP^1(kk) 
       which we indentify.
       
       Step 3. Compute the canonical series of the singular curves and the multiplier
       A at the points, i.e. the ratio between the values of the sections at P_i and Q_i.
                    
       Step 4. Computer the homogeneous ideal I of the image curve under the linear system
       
       Return the basic objects
       L=(kk,S,PQ,A,s,T) and I

     Example
         g=6;n:=3;k:=5;
         time (L,I)=randomCanonicalNodalCurve(g);
         L_0
	 (kk,S,PQ,A,s,T)=L;
	 PQ
	 A
         s;
         betti res I
         numgens T==g, degree I== 2*g-2, genus(T/I)==g   
              
///


doc ///
  Key 
    randomPrymCanonicalNodalCurve
    (randomPrymCanonicalNodalCurve,ZZ,ZZ) 
    (randomPrymCanonicalNodalCurve,ZZ,ZZ,ZZ) 
  Headline 
    get a random Prym canonical nodal curve of genus g, level n and k twisted multipliers 
  Usage
    (L,I)=randomPrymCanonicalNodalCurve(g,n,k)
  Inputs
    g: ZZ
       the desired arithmetic genus
    n: ZZ
       the desired level
    k: ZZ
       the number of twisted nodes, if not present the value is k=g.
  Outputs
    L: Sequence
       of additionally created objects (r,p,kk,S,PQ,A,s,T) with r an primitive n-th root of unity mod the prime p, 
       kk=the ground field, 
	S = homogeneous coordinate ring of P^1, PQ a list of coordinate matrices P,Q
	of the preimages of the double points, A the Prym canonical multipliers,
	s = the Prym canonical system, and T the coordinate ring of P^{g-2}
    I: Ideal
       the ideal of the random Prym canonical rational curve 
  
  Description
     Text
       Construct a Prym canonical rational curve with g double points.
       
       Step 1. Choosing an integer r and a prime p such that
       r represents an n primitive root of unity mod p.
       We then work over kk=ZZ/p and S=kk[x_0,x_1]. 
       
       Step 2.  Choose 2 times g points P_i,Q_i randomly in P^1(kk) 
       which we indentify.
       
       Step 3. Compute the canonical series of the singular curves and the multiplier
       A at the points, i.e. the ratio between the values of the sections at P_i and Q_i.
             
       Step 4. Change the ratioof the multipliers A at k of the double points by the root of unity, 
       and compute the g-1 dimensional linear system of polynomials of degree 2g-2 on PP^1
       satisfying these conditions.
       
       Step 5. Computer the homogeneous ideal I of the image curve under the linear system
       
       Return the basic objects
       L=(r,p,kk,S,PQ,A,s,T) and I

     Example
         g=6;n:=3;k:=5;
         time (L,I)=randomPrymCanonicalNodalCurve(g,n,k);
         (r,p,kk,S,PQ,A,s,T)=L;
         L_0,L_1
	 PQ
	 A
         s;
         betti res I
         numgens T==g-1, degree I== 2*g-2, genus(T/I)==g   
              
///

 

doc ///
  Key  
    canonicalMultipliers
    (canonicalMultipliers,  Matrix, Matrix)
  Headline 
    compute the canonical multipliers of a rational curves with nodes 
  Usage
    canonicalMultipliers(P,Q)
  Inputs
       P: Matrix
          coordinate matrix of g points in P^1
       Q: Matrix
          coordinate matrix of g points in P^1
  Outputs
        : Matrix
	  a matrix A of multipliers          
  Description
     Text
       Given g pairs of points P_i, Q_i, on P^1 
       compute the canonical series of the corresponding nodal curve of 
       genus g and determine the delta ratios A_i of the glueing data for the canonical bundle
       (note that A_i depends on the choice of the
       homogeneous coordinates of the point P_i and  Q_i)
///


doc ///
  Key
    syzygiesOfPrymCanonicalNodalCurve
    (syzygiesOfPrymCanonicalNodalCurve,ZZ,ZZ)
  Headline
    compute syzygies of a random Prym canonical nodal of genus g and level n  
  Usage
    syzygiesOfPyrmCanonicalNodalCurve(g,n,Printing=>true)
  Inputs
    g: ZZ
      the genus
    n: ZZ
      the level
  Outputs
     : ChainComplex
  Description
    Text
      In 
      @ HREF("http://arxiv.org/abs/0804.4616", "Farkas, Ludwig [2008]") @ 
      it is conjectured that a general smooth Prym canonical curve of {\bf even} genus $g \ge 6$ 
      has a pure resolution, i.e. $C$ embedded by $|K_C \otimes L|$ into $P^{g-2}$ has a pure resolution, where 
      $L$ is an $n$-torsion Line bundle. With this function the conjecture can be verified
      for curve of small g (and levels n) by computing the syzgies of random g-nodal Prym canonical rational curve over a finite 
      ground field and arguing by with semi-continuity of Betti numbers. 
      
      It is interesting that the verification fails along this approach for $(g,n)=(8,2)$ and $(16,2)$, but worked fine in all other cases.
    Example
       g=8
       syzygiesOfPrymCanonicalNodalCurve(8,3,Printing=>true);
       syzygiesOfPrymCanonicalNodalCurve(8,2,Printing=>true);
    Text
       Why the case of genus 8 and 2 torsion does not have expected syzygies is mysterious is to us:
    Example
       (L,I)=randomPrymCanonicalNodalCurve(8,2);
       S=L_7
       betti(fI=res I)
       pt=fI.dd_2_{0};
       CE1=ideal((fI.dd_1)*syz transpose (syz transpose pt)_{0,1});
       CE=saturate(CE1,ideal pt);
       degree CE
       betti res CE
       E=CE:I;
       betti res E
       dim E == 2, degree E == 7, genus E == 1
       dim ideal pt == 1
       degree (E+I)
    Text
      At least in the example, the syzygy scheme of the extra syzygy is a reducible half 
      canonical curve of degree 21, whose second component is an elliptc normal curve of degree 7.      
///  

doc ///
  Key
    criticalBettiNumber
    (criticalBettiNumber,ZZ,ZZ)
  Headline 
    compute the Koszul matrix for the critical Betti number in the Prym-Green conjecture
  Usage
    criticalBettiNumber(g,n)
  Inputs
    g: ZZ
      the genus, an even number, say g=2k.
    n: ZZ
      the level
  Outputs
     : Matrix
      Koszul matrix for the critical Betti number
  Description
     Text
       First an n-Prym canonical series 
       $s=H^0(C,K_C\otimes L)$ of a g-nodal rational curve and the canonical
       series omega is computed. Then an artinian reduction of the critical Kosul matrix is computed:
       Since the dual module is
       $$H^0(C,K_C) \oplus H^0(C,K_C^2\otimes L) \oplus H^0(C,K_C^3\otimes L^2) \otimes \ldots $$ 
       an artinian reduction by $s_{g-3},s_{g-2}$ has shape
       $$A=H^0(C,K_C) \oplus H^0(C,K_C^2 \otimes L) / H^0(C,K_C)<s_{g-3},s_{g-2}> \otimes \ldots$$
       The desired Koszul matrix is $koszul(k,<s_0,\ldots,s_{g-4}>) \otimes omega$ with values in $A_1$
       which is returned. The result is a $binomial(g-3,k-1) x g*binomial(g-3,k)$ matrix of binary forms
       of degree $4g-4$ with values in a $g-3$ dimensional complementary subspace of 
       $$H^0(C,K_C)<s_{g-3},s_{g-2}> \subset H^0(C,K_C^2 \otimes L) \subset K[x_0,x_1]_{4g-4}$$
                    
      In a stable version of this function the kernel of this matrix in degree 4g-4 should be returned.                 
///  


doc ///
  Key
    syzygiesOfTorsionBundle
    (syzygiesOfTorsionBundle,ZZ,ZZ,ZZ)
  Headline
    compute syzygies of a Torsion bundles in a Prym canonical embedding for a g-nodal rational random example. 
  Usage
    syzygiesOfTorsionBundle(g,n,k,Printing=>true)
  Inputs
    g: ZZ
      the even (!) genus
    n: ZZ
      the torsion level
    k: ZZ
      the exponent $2 \le k \le n-1$  
  Outputs
     : ChainComplex
  Description
    Text
       Let $(C, L)$ be a general curve of {\bf even} genus $g$ and $L \in \, Pic^0(C)$ an $n$-torsion
       bundle. In
       @ HREF("http://arxiv.org/abs", "Eisenbud, Chiodo, Farkas, Schreyer, [2012]") @ (HREF has to be corrected)
       it is conjectured that the syzygies of the module of global sections $H^0_*(P^{g-2},K_C \otimes L^k)$ as an 
       $Sym H^0(C,K_C \otimes L)$ module are pure unless $g \equiv 2 \mod \ 4$,
       $binomial(g-3,g/2-1) \equiv 1 \mod \ 2$ and $L$ is $2k-1$ torsion. In the exceptional cases we conjecture precisely one extra syzygy.
       
       With this function the conjecture can be verified for small $g$ by computing the syzygies of a random $g$-nodal example over a finite ground field, 
       and arguing by semi-continuity of Betti numbers.
    Example
       time fM=syzygiesOfTorsionBundle(8,3,2,Printing=>true);
    Text
    Example
       time fM=syzygiesOfTorsionBundle(6,3,2,Printing=>true);
       time fM=syzygiesOfTorsionBundle(6,5,2,Printing=>true);
       time fM=syzygiesOfTorsionBundle(6,5,3,Printing=>true);
///

doc ///
  Key
    verifyConjA
    (verifyConjA,ZZ,ZZ)
  Headline
    verify the Prym-Green conjecture
  Usage
    verifyConjA(g,n)
  Inputs
    g : ZZ
      the  genus, an even integer
    n : ZZ
      the level
  Outputs
     : Boolean
      if the output is true, then the Prym-Green Conjecture holds for (g,n). If the output is false, then the verification failed, but the conjecture might still be true.
  Description
    Text
       If the answer is true, then the Prym-Green Conjecture
       @ HREF("http://arxiv.org/abs/0804.4616", "Farkas, Ludwig [2010]") @
       holds for genus g and level n. In case of false the verification failed, but the conjecture could be still true.
       The options allow to ask for printing and timing. 
       
       Prinitng=>true results in
        
       1) printing of the expected betti table( of the dual) of the resolution of the Prym-canonical curve
  
       2) betti number of the critical Koszul cohomology matrix and over the ground field and the betti number of its syzygy matrix. 
          No syzygy is the conjecture.
       
       Timings=>true results in the priniting three timings:
       
       1) the time to compute the Koszul matrix as a matrix of polynomials
  
       2) the time to convert this matrix to a matrix over the ground field
  
       3) the time to compute the syzygies of this matrix.
       
       Step 3 takes a lot of time, e.g. for g=16 is took us on our machine 18 days.
    Example
       verifyConjA(8,3,Printing=>true)
       verifyConjA(8,2)
       verifyConjA(10,2,Printing=>true,Timings=>true)
///

doc ///
  Key
    verifyConjB
    (verifyConjB,ZZ,ZZ,ZZ)
  Headline
    verify Conjecture B on the syzygies of torsions bundles in Prym canonical space 
  Usage
   verifyConjB(g,n,k,Printing=>true,Timings=>true)
  Inputs
    g: ZZ
      the even (!) genus
    n: ZZ
      the torsion level
    k: ZZ
      the exponent $2 \le k \le n-1$  
  Outputs
     : Boolean
  Description
    Text
       Let $(C, L)$ be a general curve of {\bf even} genus $g$ and $L \in \, Pic^0(C)$ an $n$-torsion
       bundle. In
       @ HREF("http://arxiv.org/abs", "Eisenbud, Chiodo, Farkas, Schreyer, [2012]") @ (HREF has to be corrected)
       it is conjectured that the syzygies of the module of global sections $H^0_*(P^{g-2},K_C \otimes L^k)$ as an 
       $Sym H^0(C,K_C \otimes L)$ module are pure unless $g \equiv 2 \mod \ 4$,
       $binomial(g-3,g/2-1) \equiv 1 \mod \ 2$ and $L$ is $2k-1$ torsion. In the exceptional cases we conjecture precisely one extra syzygy.
       
       With this function the conjecture can be verified for small $g$ by computing the syzygies of a random $g$-nodal example over a finite ground field, 
       and arguing by semi-continuity of Betti numbers.

    Example
       time verifyConjB(8,3,2,Printing=>true)
       apply(3,i->verifyConjB(6,5,i+2,Timings=>true))
///


end;


--------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
--- supressed documentation
-------------------------------------------------
doc ///
  Key
    distinctPointsOfP1
    (distinctPointsOfP1,Matrix)
  Headline 
    Are these distinct points of P^1?
  Usage
     distinctPointsOfP1(P)
  Inputs
    P: Matrix
       matrix of coordinates of points in P^1
  Outputs
     : Boolean
  
  Description
     Text
       Checks whether the columns of the 2xn matrix P represent distinct 
       points of P^1 by checking that all 2x2 minors are nonzero.     
///  

doc ///
  Key
    changeMultiplier
    (changeMultiplier,Matrix,ZZ)
    (changeMultiplier, Matrix,ZZ,ZZ)
  Headline 
    change the multiplier of the double points by a factor
  Usage
    changeMultiplier(A,r)
    changeMultipliers(A,r,k)
  Inputs
    A: Matrix
       matrix of multipliers at double points
    r: ZZ
       integer representing a factor
    k: ZZ
       integer representing the number of columns which get changed
  Outputs
     : Matrix
       a new matrix of multipliers
  Description
     Text
       Given a matrix of multipliers A, the multipliers with the first k columns altered by r
       is returned. If k is not present all columns are changed by r      

///

doc ///
  Key  
   linearSeriesFromMultipliers
   (linearSeriesFromMultipliers,Sequence,Matrix)   
  Headline 
    compute the linear series of a rational curves with nodes and assigned mutipliers
  Usage
    linearSeriesFromMultipliers(PQ,A) 
  Inputs
       PQ : Sequence
             with first entrie P the coordinate matrix of g points in P^1
	     second entrie Q the coordinate matrix of further g points in P^1       
       A: Matrix
          of ratios between the values of the sections at P_i and Q_i
  Outputs
        : Matrix
	  the matrix of sections
          
  Description
     Text
       Given g pairs of points P_i, Q_i, on P^1 
       compute the linear series of degree 2g-2 on 
       the corresponding nodal curve of genus g
       from assigned multipliers A, which specify the ratio A of 
       the section of O(2g-2) at the corresponding points P_i and Q_i  
       on the normalization.
       Note that this depends on the homogeneous coordinates of the points 
       P_i and Q_i.      
///

-------------------------------------------------------------------------------------
--- end supressed documentation
-------------------------------------------------




end;
restart
loadPackage("extrasForTheKernel",Reload=>true)
uninstallPackage("NodalCurves")
installPackage("NodalCurves",RerunExamples=>true,RemakeAllDocumentation=>true);
viewHelp"NodalCurves"

loadPackage("NodalCurves",Reload=>true)
viewHelp
