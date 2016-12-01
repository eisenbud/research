newPackage(
	"NodalCurves",
    	Version => "0.2", 
    	Date => "Dezember 29, 2011",
    	Authors => {{Name => "Frank-Olaf Schreyer", 
		  Email => "schreyer@math.uni-sb.de", 
		  HomePage => "http://www.math.uni-sb.de/ag/schreyer/"}
                   },
    	Headline => "Construction of random nodal rational curves",
    	DebuggingMode => true
        )


export{canonicalMultipliers,
     getRootOfUnity,
     linearSeriesFromMultipliers,
     changeMultiplier,
     distinctPointsOfP1,
     randomPrymCanonicalNodalCurve,
     randomCanonicalNodalCurve,
     artinianReduction,koszulMap,koszulMaps,criticalKoszulDegrees,
     verifyFarkasPrymGreenConjecture,
     syzygiesOf3PrymSystem,
     syzygiesOf2PrymSystem}

distinctPointsOfP1=method()
     distinctPointsOfP1(Matrix) := P-> (
	  P2:=exteriorPower(2,P);
	  #select(toList(0..rank source P2-1),i-> P2_(0,i)==0)==0)

canonicalMultipliers=method()

canonicalMultipliers(Matrix,Matrix) := (P,Q) -> (
     S:=ring P;
     if dim S != 2 then error "not a Polynomialring in two variables";
     g:= numcols P; 
     quadrics := apply(g, i->(det(P_{i}|(transpose vars S)))*(det(Q_{i}|(transpose vars S))));
     sections := (apply(g, i -> product(g, j-> if i == j then 1_S else quadrics_j)));
     A := transpose matrix(apply(g, i ->{sub(sections_i, transpose P_{i}), sub(sections_i, transpose Q_{i})}));
     A)

linearSeriesFromMultipliers=method()

linearSeriesFromMultipliers(Sequence,Matrix) := (PQ,A) ->(
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



getRootOfUnity=method()
getRootOfUnity(ZZ,ZZ) := (n,r) -> (
     --isPrime(10009),isPrime(1009)
     --isPrime 20011
     --isPrime 30011
     if n==2 then return (30011,-1);
     r1:=r;
     Ds:=select(toList(2..floor(n/2)),d->n%d==0);
     while (L:=toList factor(r1^n-1);
           q:=last L;
           while first q > 30000 do (L=delete(q,L);q=last L);
           p:=first q;  
           while   #select(Ds,d->r^d-1%p==0)!=0 do ( r1=r1+1;
     	      L=toList factor(r1^n-1);
	      q=last L; 
	      while first q > 30000 do (L=delete(q,L);q=last L);
              p=first q);
	 p<10000) do (r1=r1+1);
     (p,r1));
TEST ///
     (p,r)=getRootOfUnity(15,20)
     assert((p,r)==(18181,21))      	  
/// 
changeMultiplier=method()

changeMultiplier(Matrix,ZZ) := (A,r) -> (
	  matrix apply(2,i->apply(rank source A,j-> if i==0 then A_(i,j) else r*A_(i,j))))

changeMultiplier(Matrix,ZZ,ZZ) := (A,r,k) -> (
	  matrix apply(2,i->apply(rank source A,j-> 
		    if i==1 and j<k then r* A_(i,j) else A_(i,j)))
	  )     


randomCanonicalNodalCurve=method()
randomCanonicalNodalCurve(ZZ) := (g)->(
     isPrime(32003);
     kk:=ZZ/32003;
     x:=symbol x;
     S:=kk[x_0,x_1];
     PQ:=(random(S^2,S^g),random(S^2,S^g));
     assert (distinctPointsOfP1(PQ_0|PQ_1)==true);
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
     P:=random(S^2,S^g);Q:=random(S^2,S^g);
     assert (distinctPointsOfP1(P|Q)==true);
     A:=canonicalMultipliers(P,Q);
     A=changeMultiplier(A,r,k);
     s:=linearSeriesFromMultipliers((P,Q),A);
     assert(rank source s==g-1);
     t:=symbol t; 
     T:=kk[t_0..t_(rank source s - 1)];
     betti(I:=ideal mingens ker map(S,T,s));
     assert (degree I==2*g-2 and genus(T/I)==g);
     L:=(r,p,kk,S,(P,Q),A,s,T);
     (L,I))

randomPrymCanonicalNodalCurve(ZZ,ZZ) := 
     (g,n) -> randomPrymCanonicalNodalCurve(g,n,g)


TEST ///
     g=8,n=4
     (L,I)=randomPrymCanonicalNodalCurve(g,n);
     (r,p,kk,S,PO,A,s,T)=L;
     assert (degree I==2*g-2 and numgens T == g-1 and genus(T/I)==g)    
///

artinianReduction=method()
artinianReduction(Ideal):= I -> (
     T:=ring I;
     kk:=coefficientRing T;
     T1:=kk[apply(codim I,j-> T_j)];
     I1:=substitute(I,T1);
     if not (dim I1==0 and degree I==degree I1) 
     then error "the last two variables do not form a regular sequence";
     (T1,I1))

koszulMap=method()
koszulMap(Ideal,ZZ,ZZ) := (I,p,q) -> (
     T:=ring I;
     betti(K:=koszul(p,vars T));
     --phi:=if q%2==0 then mingens ideal (symmetricPower(q,vars T)%I)**K else K** mingens ideal (symmetricPower(q,vars T)%I);
     betti(phi:=(mingens ideal (symmetricPower(q,vars T)%I))**K);
     TI:=T/I;
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
     TI:=T/I;
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
    

verifyFarkasPrymGreenConjecture=method(TypicalValue=>Boolean)

verifyFarkasPrymGreenConjecture(ZZ,ZZ) := (g,n) -> (
     (L,I):=randomPrymCanonicalNodalCurve(g,n,g);
     (r,p,kk,S,PQ,A,s,T):=L;
     (T1,I1):= artinianReduction(I);     
     assert(degree I1==2*g-2);
     d:=(criticalKoszulDegrees I1)_0;
     assert(d==floor(g/2)-1);
     N:=koszulMap(I1,d-1);
     rk:=(g*binomial(g-3,d-2),(g-3)*binomial(g-3,d-1)); 
     M:=transpose N;  
     sM:=syz M;
     if rank source sM=!=0  then print (rk,betti sM); 
     rank source sM==0)

verifyFarkasPrymGreenConjecture(ZZ,ZZ,ZZ) := (g,n,k) -> (
     (L,I):=randomPrymCanonicalNodalCurve(g,n,k);
     (r,p,kk,S,PQ,A,s,T):=L;
     (T1,I1):= artinianReduction(I);     
     assert(degree I1==2*g-2);
     d:=(criticalKoszulDegrees I1)_0;
     assert(d==floor(g/2)-1);
     N:=koszulMap(I1,d-1);
     rk:=(g*binomial(g-3,d-2),(g-3)*binomial(g-3,d-1));
     M:=transpose N;  
     sM:=syz M;
     if rank source sM=!=0  then print (k,betti sM); 
     rank source sM==0)

syzygiesOf3PrymSystem = method()

syzygiesOf3PrymSystem(ZZ) := g -> (
     (L,I):=randomPrymCanonicalNodalCurve(g,3,g);
     (r,p,kk,S,PQ,A,s,T):=L;
     k:=lift((g-4)/2,ZZ);
     -- build up a complex with the naively expected ranks
     rks:=apply(0..g-2,i->(g-1)*(binomial(g-3,i)-binomial(g-3,i-1)));
     L1:=apply(1..k,i->map(S^{rks_(i-1):(-i+1)},S^{rks_(i):(-i)},0));
     L1=append(L1,map(S^{rks_k:-k},S^{rks_k:-k-2},0));
     L2:=apply(1..k,i->map(S^{rks_(k-i+1):(-k-i-1)},S^{rks_(k-i):(-k-i-2)},0));
     print "naively expected syzygies:";
     print betti chainComplex (L1|L2);
     B:=changeMultiplier(A,r,g);
     --C=changeMultiplier(B,r,k);
     sA:=linearSeriesFromMultipliers(PQ,A);
     sB:=linearSeriesFromMultipliers(PQ,B);
     --sC=linearSeriesFromMultipliers(PQ,C);
     b1:=(g-1)^2-3*g+3;
     betti( m:=(syz flatten (transpose sA*sB)));
     m1:=m_{0..(b1-1)};
     ss:=symbol ss;
     TS:=T[ss_0..ss_(g-2)];	
     m2:=flatten(transpose vars TS*sub(vars T,TS))*sub(m1,TS);
     m3:=substitute(diff(transpose vars TS,m2),T);
     M3:=coker map(T^(g-1),T^{b1:-1},m3);
     print "linear strand in the example:";
     print betti (fM3:=res(M3,DegreeLimit=>0));
     fM3)

syzygiesOf2PrymSystem = method()

syzygiesOf2PrymSystem(ZZ) := g -> (
     (L,I):=randomPrymCanonicalNodalCurve(g,3,g);
     (r,p,kk,S,PQ,A,s,T):=L;
     k:=lift((g-3)/2,ZZ);
     -- build up a complex with the naively expected ranks
     rks:=apply(0..g-1,i->(g-1)*(binomial(g-2,i)-binomial(g-2,i-1)));
     L1:=apply(1..k,i->map(S^{rks_(i-1):(-i+1)},S^{rks_(i):(-i)},0));
     L1=append(L1,map(S^{rks_k:-k},S^{rks_k:-k-2},0));
     L2:=apply(1..k,i->map(S^{rks_(k-i+1):(-k-i-1)},S^{rks_(k-i):(-k-i-2)},0));
     print "naively expected syzygies:";
     print betti chainComplex (L1|L2);
     B:=canonicalMultipliers(PQ);
     sA:=linearSeriesFromMultipliers(PQ,A);
     sB:=linearSeriesFromMultipliers(PQ,B);
     --sC=linearSeriesFromMultipliers(PQ,C);
     b1:=(g-1)*g-3*g+3;
     betti( m:=(syz flatten (transpose sA*sB)));
     m1:=m_{0..(b1-1)};
     t:= symbol t;
     T=kk[t_0..t_(g-1)];
     ss:=symbol ss;
     TS:=T[ss_0..ss_(g-2)];	
     m2:=flatten(transpose vars TS*sub(vars T,TS))*sub(m1,TS);
     m3:=substitute(diff(transpose vars TS,m2),T);
     M3:=coker map(T^(g-1),T^{b1:-1},m3);
     print "linear strand in the example:";
     print betti (fM3:=res(M3,DegreeLimit=>0));
     fM3)

beginDocumentation()

doc ///
  Key
    NodalCurves
  Headline
    Construction of nodal rational curves     
  Description
    Text
      {\bf What's new:}

      {\it Version 0.1:}      
       First version

      {\bf Overview:}
         Starting from a collection of g pairs of points
         P_i, Q_i the canonical  image of the rational curves with nodes at
         these points is constructed. Similarly, embedding of these curves 
         by the linear series K tensor eta with eta an n-torsion bundle is constructed.
         The main goal is to verify Farkas' generic syzygy conjecture for small values of
         g and n. This works up to genus 14.
     
      
      

      {\bf Setup:}

      This package requires Macaulay2 version 1.3 or newer.

      Install this @TO Package@ by doing

      @TO installPackage@("NodalCurves")

      {\bf Examples:}
///
doc ///
  Key 
    randomCanonicalNodalCurve
    (randomCanonicalNodalCurve,ZZ) 
  Headline 
    Get a random canonical nodal curve of genus g, level n and k twisted multipliers 
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
	of the preimages of the double points and the cusps, A the canonical multipliers,
	s =  canonical system, and T the coordinate ring of P^{g-1}
    I: Ideal
       of the canonical rational curve 
  
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
    Get a random Prym canonical nodal curve of genus g, level n and k twisted multipliers 
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
	S = homogeneous coordinate ring of PP^1, PQ a list of coordinate matrices P,Q
	of the preimages of the double points and the cusps, A the canonical multipliers,
	s = the Prym canonical system, and T the coordinate ring of PP^{g-2}
    I: Ideal
       of the random Prym canonical rational curve 
  
  Description
     Text
       Construct a Prym canonical rational curve with g double points.
       
       Step 1. Choosing an integer r and a prime p such that
       r represents an n primitive root of unity mod p.
       We then work over kk=ZZ/p and S=kk[x_0,x_1]. 
       
       Step 2.  Choose 2 times g points P_i,Q_i randomly in PP^1(kk) 
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
       points of P^1 by checking that all 2x2 minors are nonzero.     
///   

doc ///
  Key  
    canonicalMultipliers
    (canonicalMultipliers,  Matrix, Matrix)
  Headline 
    Compute the canonical multipliers of a rational curves with nodes and cusps
  Usage
    canonicalMultipliers(P,Q)
  Inputs
       P: Matrix
          coordinate matrix of delta points in P^1
       Q: Matrix
          coordinate matrix of delta points in P^1
  Outputs
        : Matrix
	  a matrix A of multipliers          
  Description
     Text
       Given g pairs of points P_i, Q_i, on P^1 
       compute the canonical series of the corresponding nodal curve of 
       genus g and determine the delta ratios A_i
       must satisfy to be canonical (note that this depends on choosing
       homogeneous coords at each point P_i and  Q_i)
///

doc ///
  Key
    changeMultiplier
    (changeMultiplier,Matrix,ZZ)
    (changeMultiplier, Matrix,ZZ,ZZ)
  Headline 
    Change the multipier of the double points by a factor
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
    Compute the linear series of a rational curves with nodes and assigned mutipliers
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
          a prime in the Macaulay range 10000 < p< 30000
     r: ZZ
          a primitive n-th root of unity mod p          
  Description
     Text
       We compute the prime p as a larger prime factor of r^n-1.
       If the largest p in the desired range does not work, we pass to r+1 and repeat.      
     Example
       n=30
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
    Compute the Koszul map whose kernel correspond the Koszulzycles for  K_(p,q)(S/I)    
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
    Compute all Koszul maps of total degree p  for an artinian ideal I
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
       Compute all Koszul maps of total degree p  for an artinian ideal I
     Example
       g=7
       (L,I)=randomCanonicalNodalCurve(g);
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
       g=7
       (L,I)=randomCanonicalNodalCurve(g);
       (T,J)=artinianReduction(I);
       betti res J
       ps=criticalKoszulDegrees J
       (rks,N)=koszulMaps(J,ps_0);
       rks, apply(N, M->betti M)       
       N_0*N_1
       rank(ker N_0/image N_1)
///

doc ///
  Key
    verifyFarkasPrymGreenConjecture
    (verifyFarkasPrymGreenConjecture,ZZ,ZZ)
    (verifyFarkasPrymGreenConjecture,ZZ,ZZ,ZZ)
  Headline
    Verify Farkas Prym-Green Conjecture for genus g and level n  
  Usage
    verifyFarkasPrymGreenConjecture(g,n)
    verifyFarkasPrymGreenConjecture(g,n,k)
  Inputs
    g: ZZ
      the genus
    n: ZZ
      the level
    k: ZZ
      number of altered multipliers
  Outputs
     : Boolean
  Description
    Text
       Gavril Farkas conjectures that a general smooth curve C of genus g embedded by
       a line bundle $K_C \otimes \, L$ with $L \in \, Pic^0(C)$ n-torsion
       has for even genus a pure resolution. For given genus g and level n, this program
       attemps the verification by computing the syzygies of a Prym canonical model at the 
       appropiate step for a nodal rational curve of genus g which has 
       with k multipliers altered by root of unity.
       
       Step 1. Choice of a random Prym canonically embedded nodal curve.
       
       Step 2. Computation of the desired Koszul homology matrices of an artinian reduction
       
       Step 3. Verification of the maximal rank of the appropiate matrix.
       This step is heavy. For genus 14 about 45 minutes, for genus 16 an yet unknown time.
    Example
       verifyFarkasPrymGreenConjecture(8,3,6)
       g=8
       apply(toList(3..g),k->(k,verifyFarkasPrymGreenConjecture(g,3,k)))
    Text
       Why the case of genus 8 and 2 torsion does not work is mysterious:
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
      cononical curve of degree 21, whose second component is an elliptc normal curve of degree 7.      
///  

doc ///
  Key
    syzygiesOf3PrymSystem
    (syzygiesOf3PrymSystem,ZZ)
  Headline
    Verify Farkas Conjecture on 3 Prym systems 
  Usage
    syzygiesOf3PrymSystem(g)
  Inputs
    g: ZZ
      an even (!) genus
  Outputs
     : ChainComplex
  Description
    Text
       Gavril Farkas conjectures that a general smooth curve C of genus g and $L \in \, Pic^0(C)$ 3-torsion
       the syzygies of 
       the line bundle $K_C \otimes \, L^2$ as an $Sym H^0(K_C \otimes \, L)$- module
       are pure in case $g \equiv 0 mod 4$. 
       The function verifies this for small g, by considering nodal raional curves.
       This proves the effectiveness of certain Koszul divisors in the moduli space of 3-Prym curves.
       
       Step 1. Choice of a random 3-Prym canonically embedded nodal curve.
       
       Step 2. Print of the expected Betti table.
       
       Step 3. Computation of the linear strand of resolution $K_C \otimes L^2$
    Example
       time fM=syzygiesOf3PrymSystem 8;
    Text
       The case of $g \equiv 2 mod 4$ has an extra syzygy due to the skew symmetry of a certain Koszul matrix
    Example
       time fM=syzygiesOf3PrymSystem 6;
/// 

doc ///
  Key
    syzygiesOf2PrymSystem
    (syzygiesOf2PrymSystem,ZZ)
  Headline
    Verify conjecture on 2 Prym systems 
  Usage
    syzygiesOf2PrymSystem(g)
  Inputs
    g: ZZ
      an odd (!) genus
  Outputs
     : ChainComplex
  Description
    Text
       We conjectures that a general smooth curve C of genus g and $L \in \, Pic^0(C)$ 2-torsion
       the syzygies of 
       the line bundle $K_C \otimes \, L$ as an $Sym H^0(K_C)$- module
       are pure in case $g \equiv 1 mod 2$. 
       The function verifies this for small g, by considering nodal rational curves.
       This proves the effectiveness of certain Koszul divisors in the moduli space of 2-Prym curves.
       
       Step 1. Choice of a random 2-Prym canonically embedded nodal curve.
       
       Step 2. Print of the expected Betti table.
       
       Step 3. Computation of the linear strand of resolution $K_C \otimes L$
    Example
       time fM=syzygiesOf2PrymSystem 5;
       time fM=syzygiesOf2PrymSystem 7;
       time fM=syzygiesOf2PrymSystem 9;

///

end;
restart
uninstallPackage("NodalCurves")
installPackage("NodalCurves",RerunExamples=>true,RemakeAllDocumentation=>true);
viewHelp"NodalCurves"
loadPackage("NodalCurves",Reload=>true)

time fM=syzygiesOf3PrymSystem 8;
time fM=syzygiesOf3PrymSystem 10;     -- used 10.9318 seconds
--g=time fM=syzygiesOf3PrymSystem 12;     -- used 876.568/60 seconds  = 14.6 minutes
--naively expected syzygies:
--        0  1   2   3   4   5   6   7  8  9
--total: 11 88 297 528 462 462 528 297 88 11
--    0: 11 88 297 528 462   .   .   .  .  .
--    1:  .  .   .   .   . 462 528 297 88 11
--linear strand in the example:
--        0  1   2   3   4
--total: 11 88 297 528 462
--    0: 11 88 297 528 462


--time fM=syzygiesOf2PrymSystem 11;      -- used 562.46 seconds = 9.37 minutes
--naively expected syzygies:
--        0  1   2   3   4   5   6   7  8  9
--total: 10 80 270 480 420 420 480 270 80 10
--    0: 10 80 270 480 420   .   .   .  .  .
--    1:  .  .   .   .   . 420 480 270 80 10
--linear strand in the example:
--        0  1   2   3   4
--total: 10 80 270 480 420
--    0: 10 80 270 480 420


time verifyFarkasPrymGreenConjecture(8,2,8)
time verifyFarkasPrymGreenConjecture(10,2,10)   -- used 1.89503 seconds
time verifyFarkasPrymGreenConjecture(12,2,12)   -- used 29.763 seconds
-- time verifyFarkasPrymGreenConjecture(14,2,14)   -- used 2608.77 seconds = 43.4 minutes

time fM=syzygiesOf3PrymSystem 14; 

time (L,I)=randomPrymCanonicalNodalCurve(12,2,12);
time betti res(I,DegreeLimit=>1)

(L,I)=randomPrymCanonicalNodalCurve(8,3,8);
betti res I

(L,I)=randomPrymCanonicalNodalCurve(8,4,8);
betti res I

h=6
g=2*h
(L,I)=randomPrymCanonicalNodalCurve(g,2,g);
time betti res(I,LengthLimit=>h-2)
