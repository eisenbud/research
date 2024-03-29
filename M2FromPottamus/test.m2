newPackage(
	"NodalCuspidalCurves",
   	Version => "0.2", 
   	Date => "July 14, 2010",
   	Authors => {{Name => "Frank-Olaf Schreyer", 
		 Email => "schreyer@math.uni-sb.de", 
		 HomePage => "http://www.math.uni-sb.de/ag/schreyer/"}
                  },
   	Headline => "Construction of random nodal-cuspidal rational curves",
   	DebuggingMode => true
       )


export{canonicalMultipliers,getRootOfUnity,linearSeriesFromMultipliers,changeMultiplier,
    distinctPointsOfP1,randomPrymCanonicalNodalCuspidalCurve,
    randomCanonicalNodalCuspidalCurve,artinianReduction,koszulMap,koszulMaps,
    criticalKoszulDegrees,verifyFarkasPrymGreenConjecture,Printing}

distinctPointsOfP1=method()
    distinctPointsOfP1(Matrix) := P-> (
	 P2:=exteriorPower(2,P);
	 #select(toList(0..rank source P2-1),i-> P2_(0,i)==0)==0)

canonicalMultipliers=method()
canonicalMultipliers(Matrix,Matrix,Matrix) := (P,Q,R) -> (
    S:=ring P;
    if dim S != 2 then error "not a Polynomialring in two variables";
    delta:= numcols P; kappa := numcols R;
    g := delta+kappa;
    quadrics2 := apply(kappa, i-> (det(R_{i}|(transpose vars S)))^2);
    quadrics1 := apply(delta, i->(det(P_{i}|(transpose vars S)))*(det(Q_{i}|(transpose vars S))));
    quadrics := join(quadrics1,quadrics2);
    sections := (apply(g, i -> product(g, j-> if i == j then 1_S else quadrics_j)));
    A := transpose matrix(apply(delta, i ->{sub(sections_i, transpose P_{i}), sub(sections_i, transpose Q_{i})}));
    B := map(S^2,S^kappa,transpose matrix(apply(kappa,i->{sub(diff (matrix{{S_1,-S_0}},sections_(i+delta)), transpose R_{i})})));
    (A,B))


linearSeriesFromMultipliers=method()
linearSeriesFromMultipliers(Sequence) := (PQRAB) ->(
    P:=PQRAB_0; Q:=PQRAB_1; R:=PQRAB_2; A:=PQRAB_3; B:=PQRAB_4;
    S := ring P;
    delta := numcols P; 
    kappa := numcols R;
    g := delta+kappa;
    Bs := basis(2*g-2, S);
    jB :=jacobian Bs; 
    MR :=matrix apply(kappa, i->flatten entries((transpose B_{i})*sub(jB,transpose R_{i})));
    MP := matrix(apply(numcols P, i->flatten entries(A_(1,i)*(sub(Bs, transpose P_{i})))));
    MQ := matrix(apply(numcols P, i->flatten entries(A_(0,i)*(sub(Bs, transpose Q_{i})))));
    sy := syz(MP-MQ||MR);
    ell:= rank source sy;
    map(S^1, S^{ell:-2*g+2}, Bs*sy)
    )
linearSeriesFromMultipliers(Sequence,Sequence) := (PQR,AB) ->(
    P:=PQR_0; Q:=PQR_1; R:=PQR_2; A:=AB_0; B:=AB_1;
    S := ring P;
    delta := numcols P; 
    kappa := numcols R;
    g := delta+kappa;
    Bs := basis(2*g-2, S);
    jB :=jacobian Bs; 
    MR :=matrix apply(kappa, i->flatten entries((transpose B_{i})*sub(jB,transpose R_{i})));
    MP := matrix(apply(numcols P, i->flatten entries(A_(1,i)*(sub(Bs, transpose P_{i})))));
    MQ := matrix(apply(numcols P, i->flatten entries(A_(0,i)*(sub(Bs, transpose Q_{i})))));
    sy := syz(MP-MQ||MR);
    ell:= rank source sy;
    map(S^1, S^{ell:-2*g+2}, Bs*sy)
    )

getRootOfUnity=method()
getRootOfUnity(ZZ,ZZ) := (n,r) -> (
    --isPrime(10009),isPrime(1009)
    if n==2 then return (10009,-1);
    r1:=r;
    Ds:=select(toList(2..floor(n/2)),d->n%d==0);
    while (L:=toList factor(r1^n-1);
          q:=last L;
          while first last L > 20000 do (L=delete(q,L);q=last L);
          p:=first q;  
          while   #select(Ds,d->r^d-1%p==0)!=0 do ( r1=r1+1;
    	     L=toList factor(r1^n-1);
	     q=last L; 
	     while first last L > 20000 do (L=delete(q,L);q=last L);
             p=first q);
	p<5000) do (r1=r1+1);
    (p,r1));
TEST ///
    (p,r)=getRootOfUnity(15,20)
    assert((p,r)==(3001,20))      	 
/// 
changeMultiplier=method()
changeMultiplier(Matrix,ZZ) := (A,r) -> (
	 matrix apply(2,i->apply(rank source A,j-> if i==0 then A_(i,j) else r*A_(i,j))))
changeMultiplier(Matrix,ZZ,ZZ) := (A,r,k) -> (
	 matrix apply(2,i->apply(rank source A,j-> 
		   if i==1 and j<k then r* A_(i,j) else A_(i,j)))
	 )     
TEST ///
    n=3
    (p,r)=getRootOfUnity(3,110)
    kk=ZZ/p   
    S=kk[x_0,x_1]
    delta=5,kappa=3,g=delta+kappa
    PQR=(random(S^2,S^delta),random(S^2,S^delta),matrix{{1,0,1},{0,1,1}}**S)
    assert (distinctPointsOfP1(PQR_0|PQR_1|PQR_2)==true)
    P=PQR_0
    AB=canonicalMultipliers(PQR)
    s=linearSeriesFromMultipliers(PQR,AB);
    assert (rank source s == g)
    T=kk[t_0..t_(rank source s - 1)]
    betti(I=ideal mingens ker map(S,T,s))
    assert (degree I==2*g-2 and genus(T/I)==g )
    A=changeMultiplier(AB_0,r,delta)
    B=AB_1
    s=linearSeriesFromMultipliers(PQR,(A,B));
    assert(rank source s==g-1) 
    T=kk[t_0..t_(rank source s - 1)]
    betti(I=ideal mingens ker map(S,T,s))
    assert (degree I==2*g-2 and genus(T/I)==g)
--     time betti res (I,DegreeLimit=>1)
///

randomCanonicalNodalCuspidalCurve=method()
randomCanonicalNodalCuspidalCurve(ZZ,ZZ) := (g,kappa)->(
    isPrime(32003);
    kk:=ZZ/32003;
    S=kk[x_0,x_1];
    delta:=g-kappa;
    R:=matrix{{1,0,1},{0,1,1}}**S;
    R=if kappa <=3 then R_{0..kappa-1} else R|random(S^2,S^(kappa-3));
    PQR:=(random(S^2,S^delta),random(S^2,S^delta),R);
    assert (distinctPointsOfP1(PQR_0|PQR_1|PQR_2)==true);
    AB:=canonicalMultipliers(PQR);
    s:=linearSeriesFromMultipliers(PQR,AB);
    assert(rank source s==g); 
    T:=kk[t_0..t_(rank source s - 1)];
    betti(I:=ideal mingens ker map(S,T,s));
    assert (degree I==2*g-2 and genus(T/I)==g);
    L:=(kk,S,PQR,AB,s,T);
    (L,I))


randomPrymCanonicalNodalCuspidalCurve=method()

randomPrymCanonicalNodalCuspidalCurve(ZZ,ZZ) := (g,n)->(
    (p,r):=getRootOfUnity(n,100+random(100));     
    kk:=ZZ/p;
    S:=kk[x_0,x_1];
    kappa:=3,delta:=g-kappa;
    PQR:=(random(S^2,S^delta),random(S^2,S^delta),matrix{{1,0,1},{0,1,1}}**S);
    assert (distinctPointsOfP1(PQR_0|PQR_1|PQR_2)==true);
    AB:=canonicalMultipliers(PQR);
    A=changeMultiplier(AB_0,r,delta);
    B=AB_1;
    s:=linearSeriesFromMultipliers(PQR,(A,B));
    assert(rank source s==g-1); 
    T:=kk[t_0..t_(rank source s - 1)];
    betti(I:=ideal mingens ker map(S,T,s));
    assert (degree I==2*g-2 and genus(T/I)==g);
    L:=(r,p,kk,S,PQR,(A,B),s,T);
    (L,I))



randomPrymCanonicalNodalCuspidalCurve(ZZ,ZZ,ZZ) := (g,n,kappa)->(
    (p,r):=getRootOfUnity(n,random(200));     
    kk:=ZZ/p;
    S:=kk[x_0,x_1];
    delta:=g-kappa;
    R:=matrix{{1,0,1},{0,1,1}}**S;
    R=if kappa <=3 then R_{0..kappa-1} else R|random(S^2,S^(kappa-3));
    PQR:=(random(S^2,S^delta),random(S^2,S^delta),R);
    assert (distinctPointsOfP1(PQR_0|PQR_1|PQR_2)==true);
    AB:=canonicalMultipliers(PQR);
    A=changeMultiplier(AB_0,r,delta);
    B=AB_1;
    s:=linearSeriesFromMultipliers(PQR,(A,B));
    assert(rank source s==g-1); 
    T:=kk[t_0..t_(rank source s - 1)];
    betti(I:=ideal mingens ker map(S,T,s));
    assert (degree I==2*g-2 and genus(T/I)==g);
    L:=(r,p,kk,S,PQR,(A,B),s,T);
    (L,I))

TEST ///
    g=8,n=4
    (L,I)=randomPrymCanonicalNodalCuspidalCurve(g,n);
    (r,p,kk,S,POR,AB,s,T)=L;
    assert (degree I==2*g-2 and numgens T == g-1 and genus(T/I)==g)    
///

artinianReduction=method()
artinianReduction(Ideal):= I -> (
    T:=ring I;
    kk:=coefficientRing T;
    T1:=kk[apply(codim I,j-> T_j)];
    I1:=substitute(I,T1);
    assert(dim I1==0 and degree I==degree I1);
    (T1,I1))

koszulMap=method()
koszulMap(Ideal,ZZ,ZZ) := (I,p,q) -> (
    T:=ring I;
    betti(K:=koszul(p,vars T));
    --phi:=if q%2==0 then mingens ideal (symmetricPower(q,vars T)%I)**K else K** mingens ideal (symmetricPower(q,vars T)%I);
    betti(phi:=(mingens ideal (symmetricPower(q,vars T)%I))**K);
    TI=T/I;
    betti(phir:=lift(substitute(phi,TI),T));
    m:=mingens ideal( symmetricPower(q+1,vars T)%I);
    h:=hilbertFunction(q+1,I);
    assert(h>0);
    betti(M:=contract(m_0,phir));
    scan(h-1,i->M=M||contract(m_(i+1),phir));
    substitute(M,coefficientRing T))     

koszulMap(Ideal,ZZ) := (I,p) -> ( T:=ring I;
    betti(K:=koszul(p,vars T));
    --phi:=if q%2==0 then mingens ideal (symmetricPower(q,vars T)%I)**K else K** mingens ideal (symmetricPower(q,vars T)%I);
    betti(phi:=K**vars T);
    TI=T/I;
    betti(phir:=lift(substitute(phi,TI),T));
    m:=mingens ideal( symmetricPower(2,vars T)%I);
    h:=hilbertFunction(2,I);
    assert(h>0);
    betti(M:=contract(m_0,phir));
    scan(h-1,i->M=M||contract(m_(i+1),phir));
    substitute(M,coefficientRing T)) 


koszulMaps=method()
koszulMaps(Ideal,ZZ) := (I,p) -> (
    assert(dim I==0);
    T:=ring I;
    H:=select(apply(degree I, k-> hilbertFunction(k,I)),j->j=!=0);
    select(toList(2..H_1+#H-1),i->sum(#H,j->(-1)^j*H_j*binomial(H_1,i-j))==0);
    rK:=apply(#H,j->H_(#H-j-1)*binomial(H_1,p-#H+j+1));
    maps:=apply(#H-1,j->koszulMap(I,p-#H+2+j,#H-2-j));
    (rK,maps)) 


criticalKoszulDegrees=method()
criticalKoszulDegrees(Ideal) := I -> (
    assert(dim I==0);
    T:=ring I;
    H:=select(apply(degree I, k-> hilbertFunction(k,I)),j->j=!=0);
    ps:=select(toList(2..H_1+#H-1),i->sum(#H,j->(-1)^j*H_j*binomial(H_1,i-j))==0);
    --assert(#ps>1);
    ps)
TEST ///
    g=7
    (L,I)=randomCanonicalNodalCuspidalCurve(g,3);
    (T1,I1)=artinianReduction(I);
    ps=criticalKoszulDegrees(I1);
    (rk,N)=koszulMaps(I1,ps_0);
    rK, apply(N,n->betti n)
    assert(N_0*N_1==0 and N_1*N_2==0)   
///
verifyFarkasPrymGreenConjecture=method(TypicalValue=>boolean,Options=>{Printing=>false})
verifyFarkasPrymGreenConjecture(ZZ,ZZ) := opt->(g,n) -> (
    (L,I):=randomPrymCanonicalNodalCuspidalCurve(g,n,3);
    (r,p,kk,S,PQR,AB,s,T):=L;
    if opt.Printing then print(n,kk,p,r);
    (T1,I1):= artinianReduction(I);     
    assert(degree I1==2*g-2);
    d=(criticalKoszulDegrees I1)_0;
    assert(d==floor(g/2)-1);
    N:=koszulMap(I1,d-1);
    rk:=(g*binomial(g-3,d-2),(g-3)*binomial(g-3,d-1));
    --if opt.Printing  then 
    print (rk,betti N);
    M:=transpose N;  
    sM:=syz M;
    rank source sM==0)


doc ///
 Key
   verifyFarkasPrymGreenConjecture
   (verifyFarkasPrymGreenConjecture,ZZ,ZZ)
 Headline
   Verify Farkas Prym-Green Conjecture for genus g and level n
 Usage
   verifyFarkasPrymGreenConjecture(g,n)
 Inputs
   g: ZZ
     the genus
   n: ZZ
     the level
 Outputs
    : Boolean
 Description
   Text
      Gavril Farkas conjectures that a general smooth curve C of genus g embedded by
      a line bundle $K_C \otimes L$ with $L \in Pic^0(C)$ n-torsion
      has for even genus a pure resolution. For given genus g and level n, this program
      attemps the verification by computing the syzygies of a Prym canonical model at the 
      appropiate step for a nodal cuspidal rational curve of genus g.

      Step 1. Choice of a random Prym canonically embedded nodal-cuspidal curve.

      Step 2. Computation of the desired Koszul homology matrices of an artinian reduction

      Step 3. Verification of tha maximal rank of the appropiate matrix.
      This step is heavy. For genus 14 about 45 minutes, for genus 16 an yet unknown time.
///  



beginDocumentation()

doc ///
 Key
   NodalCuspidalCurves
 Headline
   Construction of nodal cuspidal rational curves     
 Description
   Text
     {\bf What's new:}

     {\it Version 0.1:}      
      First version

     {\bf Overview:}
        Starting from a collection of kappa points R_j and delta pairs of points
        P_i, Q_i the canonical  image of the rational curves with cusps and nodes at
        these points is constructed. Similarly, embedding of these curves 
        by the linear series K tensor eta with eta an n-torsion bundle is constructed.
        The main goal is to verify Farkas' generic syzygy conjecture for small values of
        g=kappa+delta and n. This works up to genus 14.




     {\bf Setup:}

     This package requires Macaulay2 version 1.3 or newer.

     Install this @TO Package@ by doing

     @TO installPackage@("NodalCuspidalCurves")

     {\bf Examples:}
///

doc ///
 Key 
   randomCanonicalNodalCuspidalCurve
   (randomCanonicalNodalCuspidalCurve,ZZ,ZZ) 
 Headline 
   Get a random Prym canonical nodal cuspidal curve of genus g and level n  
 Usage
   (L,I)=randomCanonicalNodalCuspidalCurve(g,kappa)
 Inputs
   g: ZZ
      the desired arithmetic genus
   kappa: ZZ
      the desired number of cusps
 Outputs
    L: Sequence 
    	a sequence of additionally created objects (kk,S,PQR,AB,s,T) with kk=the ground field, 
	S = homogeneous coordinate ring of PP^1, PQR a list of coordinate matrices P,Q,R
	of the preimages of the double points and the cusps, AB the canonical multipliers,
	s = the canonical system, and T the coordinate ring of PP^{g-1}
    I: Ideal
       of the nodal cuspidal rational canonical curve

 Description
    Text
      Construct a canonical rational curve with delta=g-kappa double points and kappa cusps.

      Step 1. Choose 2 times delta=points P_i,Q_i randomly in PP^1(kk) 
      which we indentify and kappa cusps at in PP^1.

      Step 2. Compute the canonical series of the singular curves and the multiplier
      A, B at the points, i.e. the ratio between the values of the sections at P_i and Q_i
      respectively the ratios between the partials at the cusps.

      Step 3. Computer the homogeneous ideal I of the image curve under the linear syst

      Return the basic objects
      L=(kk,S,PQR,AB,s,T) and I

    Example
        g=6;kappa=3;
        time (L,I)=randomCanonicalNodalCuspidalCurve(g,kappa);
        (kk,S,PQR,AB,s,T)=L;
        kk,S
	PQR
	AB
        s;
        betti res I
        numgens T==g, degree I== 2*g-2, genus(T/I)==g   
///

doc ///
 Key 
   randomPrymCanonicalNodalCuspidalCurve
   (randomPrymCanonicalNodalCuspidalCurve,ZZ,ZZ) 
 Headline 
   Get a random Prym canonical nodal cuspidal curve of genus g and level n  
 Usage
   (L,I)=randomPrymCanonicalNodalCuspidalCurve(g,n)
 Inputs
   g: ZZ
      the desired arithmetic genus
   n: ZZ
      the desired level
 Outputs
   L: Sequence
      of additionally created objects (r,p,kk,S,PQR,AB,s,T) with r an primitive n-th root of unity mod the prime p, 
      kk=the ground field, 
	S = homogeneous coordinate ring of PP^1, PQR a list of coordinate matrices P,Q,R
	of the preimages of the double points and the cusps, AB the canonical multipliers,
	s = the canonical system, and T the coordinate ring of PP^{g-1}
   I: Ideal
      of the random Prym canonical rational curve 

 Description
    Text
      Construct a Prym canonical rational curve with g-3 double points and 3 cusps.

      Step 1. Choosing an integer r and a prime p such that
      r represents an n primitive root of unity mod p.
      We then work over kk=ZZ/p and S=kk[x_0,x_1]. 

      Step 2.  Choose 2 times delta=g-3 points P_i,Q_i randomly in PP^1(kk) 
      which we indentify and three cusps at 0 1 and infty in PP^1.

      Step 3. Compute the canonical series of the singular curves and the multiplier
      A, B at the points, i.e. the ratio between the values of the sections at P_i and Q_i
      respectively the ratios between the partials at the cusps.

      Step 4. Change the ration at the double points by the root of unity, 
      and compute the g-1 dimensional linear system of polynomials of degree 2g-2 on PP^1
      satisfying these conditions.

      Step 5. Computer the homogeneous ideal I of the image curve under the linear syst

      Return the basic objects
      L=(r,p,kk,S,PQR,AB,s,T) and I

    Example
        g=8;n=3;
        time (L,I)=randomPrymCanonicalNodalCuspidalCurve(g,n);
        (r,p,kk,S,PQR,AB,s,T)=L;
         r,p
	 PQR
	 AB
         s;
         time betti res I
         numgens T==g-1, degree I== 2*g-2, genus(T/I)==g   
///

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
      Checks whether the columns of the 2xn matrix P repesent distinct 
      points of P^1 by checkingthat all 2x2 minors are nonzero.     
///   

doc ///
 Key  
   canonicalMultipliers
   (canonicalMultipliers,  Matrix, Matrix, Matrix) 
 Headline 
   Compute the canonical multipliers of a rational curves with nodes and cusps
 Usage
   canonicalMultipliers(P,Q,R)
 Inputs
      P: Matrix
         coordinate matrix of delta points in P^1
      Q: Matrix
         coordinate matrix of delta points in P^1
      R: Matrix
         coordinate matrix of kappa points in P^1
 Outputs
       : Sequence
	 pair (A,B) of matrices of multipliers

 Description
    Text
      Given delta pairs of points P_i, Q_i, on P^1 and kappa points R_j 
      compute the canonical series of the coreesponding nodal cuspidal curve of 
      genus g=delta+kappa and determine the delta ratios A_i and kappa ratio
      B_j of the partials which the sections of O(2g-2)
      must satisfy to be canonical (note that this depends on choosing
      homogeneous coords at each point P_i, Q_i and R_j)
///

doc ///
 Key
   changeMultiplier
   (changeMultiplier,Matrix,ZZ)
   (changeMultiplier, Matrix,ZZ,ZZ)
 Headline 
   Change the multipier of double points by a factor
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
  (linearSeriesFromMultipliers, Sequence)
  (linearSeriesFromMultipliers, Sequence,Sequence)  
 Headline 
   Compute the linear series of a rational curves with nodes and cusps and assigned mutipliers
 Usage
   linearSeriesFromMultipliers(PQRAB)
   linearSeriesFromMultipliers(PQR,AB)
 Inputs
      PQR: Sequence
      AB: Sequence
          or
      PQRAB: Sequence
         with first entrie P the coordinate matrix of delta points in P^1
	 second entrie Q the coordinate matrix of delta points in P^1
      	 third entrie R coordinate matrix of kappa points in P^1
         fourth entrie A matrix of ratios between the values of the sections at P_i and Q_i
         fith entrie B matrix ratios between the partials of the sections at R_j
 Outputs
       : Matrix
	 the matrix of sections

 Description
    Text
      Given delta pairs of points P_i, Q_i, on P^1 and kappa points R_j 
      compute the linear series of degree 2g-2 canonical series on 
      the corresponding nodal-cuspidal curve of genus g=delta+kappa 
      from assigned multipliers A and B, which specify the ratio A of 
      the section of O(2g-2) at the corresponding points P_i and Q_i  
      on the normalization and B the ration of the partials at the cusps R_i.
      Note that this depends on the homogeneous coordinates of the points 
      P_i,Q_i and R_j.      
///
doc ///
 Key  
  getRootOfUnity
  (getRootOfUnity, ZZ,ZZ) 
 Headline 
  Find a prime p with an n-th root of unity r in Z/p
 Usage
   getRootOfUnity(n,r)
 Inputs
   n: ZZ
      the exponent of the root of unity
   r: ZZ
      tentative root of unity
 Outputs
    p: ZZ
         a prime in the Macaulay range <2^{15}
    r: ZZ
         a primitive n-th root of unity mod p          
 Description
    Text
      We compute the prime p as a larger prime factor of r^n-1.
      If the largest p in the desired range does not work, we pass to r+1 and repeat.      
    Example
      n=12
      (p,r)=getRootOfUnity(n,5)
      factor(r^n-1)
      	   
///
doc ///
 Key
   artinianReduction
   (artinianReduction,Ideal)
 Headline
   Compute an artinian quotient of an Cohen-Macaulay ideal
 Usage
   (T,J)=artinianQuotient(I)
 Inputs
   I: Ideal
 Outputs
   T: PolynomialRing
   J: Ideal 
 Description
    Text
      Computes the artinian quotient T/J in case the last dim I variables form a regular sequence
      mod I
    Example
      R=ZZ/101[x_0..x_3];
      I=minors(2,matrix{{x_3,x_0,x_1},{x_0,x_1,x_2}})
      artinianReduction(I)
///

doc ///
 Key
   koszulMap
   (koszulMap,Ideal,ZZ,ZZ)
 Headline
   Compute the Koszul map whose kernel correspond the Koszulzycles for  K_(p,q)(S/I)    
 Usage
   kozsulMap(I,p,q)
 Inputs
   I: Ideal
   p: ZZ 
      homological degree
   q: ZZ
     internal degree
 Outputs
   : Matrix
     Koszul matrix over the coefficient ring 
 Description
    Text
      Computes the Koszul matrix
      $\Lambda^p V \otimes\, (ring/I)_q \to \Lambda^{p-1} V \otimes \, (ring/I)_{q+1}$ 
      for the coordinate ring mod I
    Example
      kk=ZZ/101;
      R=kk[x_0..x_3];
      betti(I=minors(3,random(R^4,R^{2:-1,-2})));
      betti res I
      N1=koszulMap(I,2,3);
      N2=koszulMap(I,3,2);
      N1*N2
      rank (ker N1/image N2)
///

doc ///
 Key
   koszulMaps
   (koszulMaps,Ideal,ZZ)
 Headline
   Compute all Koszul maps of total degree p  for an artinian ideal I
 Usage
   (L,N)=koszulMaps(I,p)
 Inputs
   I: Ideal
   p: ZZ 
      total degree
 Outputs
   L: List
      sizes of the Koszul matrices,
   N: List 
      of correspondence Koszul matrices over the ground field 
 Description
    Text
      Compute all Koszul maps of total degree p  for an artinian ideal I
    Example
      g=7,kappa=3
      (L,I)=randomCanonicalNodalCuspidalCurve(g,kappa);
      (T,J)=artinianReduction(I);
      betti res J
      ps=criticalKoszulDegrees J
      (rks,N)=koszulMaps(J,ps_0);
      rks, apply(N, M->betti M)       
      N_0*N_1
      rank (ker N_0/image N_1)
///

doc ///
 Key
   criticalKoszulDegrees
   (criticalKoszulDegrees,Ideal)
 Headline
   Compute all d with $\sum_{p+q=d} (-1)^q dim K_{p,q}(S/I)==0$ for an artinian ideal I
 Usage
   criticalKoszulDegrees(I)
 Inputs
   I: Ideal
 Outputs
    : List
      of degrees 
 Description
    Text
      Compute all d>1 with $\sum_{p+q=d} (-1)^q dim K_{p,q}(S/I)==0$ for an artinian ideal I
    Example
      g=7,kappa=3
      (L,I)=randomCanonicalNodalCuspidalCurve(g,kappa);
      (T,J)=artinianReduction(I);
      betti res J
      ps=criticalKoszulDegrees J
      (rks,N)=koszulMaps(J,ps_0);
      rks, apply(N, M->betti M)       
      N_0*N_1
      rank (ker N_0/image N_1)
///


end;



restart
uninstallPackage("NodalCuspidalCurves")
installPackage("NodalCuspidalCurves",RerunExamples=>true,RemakeAllDocumentation=>true);
viewHelp"NodalCuspidalCurves"


time verifyFarkasPrymGreenConjecture(10,2,Printing=>true) -- used 2.51 seconds
time verifyFarkasPrymGreenConjecture(12,2,Printing=>true) -- used 22.39 seconds
time verifyFarkasPrymGreenConjecture(14,2,Printing=>true) -- used 2718.25 seconds
time verifyFarkasPrymGreenConjecture(16,2,Printing=>true)

end
installPackage "m2test4"
