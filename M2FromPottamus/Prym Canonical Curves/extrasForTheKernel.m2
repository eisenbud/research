newPackage(
	"extrasForTheKernel",
    	Version => "0.1", 
    	Date => "March 7, 2012",
    	Authors => {{Name => "Frank-Olaf Schreyer", 
		  Email => "schreyer@math.uni-sb.de", 
		  HomePage => "http://www.math.uni-sb.de/ag/schreyer/"}
                   },
    	Headline => "Some little extras for the kernel of Macaulay2",
    	DebuggingMode => true
        )


export{nextPrime,
     getRootOfUnity,
     randomKRationalPoint,
     artinianReduction,
     expectedSyzygies,
     koszulMap,
     koszulMaps,
     criticalKoszulDegrees}

nextPrime=method()
nextPrime(ZZ):=n->(
      p:=if n%2==0 then n+1 else n;
      while not isPrime(p) do p=p+2;
      p)



getRootOfUnity=method()
getRootOfUnity(ZZ,ZZ) := (n,r) -> (
     if n==2 then return (nextPrime(10^4+random(10^4)),-1);
     r1:=r;
     Ds:=select(toList(2..floor(n/2)),d->n%d==0);
     while (L:=toList factor(r1^n-1);
           q:=last L;
           while first last L > 20000 do (L=delete(q,L);q=last L);
           p:=first q;  
           while   #select(Ds,d->r^d-1%p==0)!=0 do ( r1=r1+1;
     	      L=toList factor(r1^n-1);
	      q=last L; 
	      while first last L > 20000 do (L=delete(q,L);q=last L);
              p=first q);
	 p<10000) do (r1=r1+1);
     (p,r1));
TEST ///
     (p,r)=getRootOfUnity(15,20)
     assert((p,r)==(18181,21))      	  
/// 
randomKRationalPoint=method()
randomKRationalPoint(Ideal):=I->(
     R:=ring I;
     if char R == 0 then error "expected a finite ground field";
     if not class R === PolynomialRing then error "expected an ideal in a polynomial ring";
     if not isHomogeneous I then error "expected a homogenous ideal";
     n:=dim I;
     if n<=1 then error "expected a positive dimensional scheme";
     c:=codim I;Rs:=R;Re:=R;f:=I;
     if not c==1 then (
     -- projection onto a hypersurface
     parametersystem:=ideal apply(n,i->R_(i+c));
     if not dim(I+parametersystem)== 0 then return print "make coordinate change";
     kk:=coefficientRing R;
     Re=kk[apply(dim R,i->R_i),MonomialOrder => Eliminate (c-1)];
     rs:=(entries selectInSubring(1,vars Re))_0;
     Rs=kk[rs];
     f=ideal sub(selectInSubring(1, gens gb sub(I,Re)),Rs);
     if not degree I == degree f then return print "make coordinate change");
     H:=0;pts:=0;pts1:=0;trial:=1;pt:=0;ok:=false;
     while (
       H=ideal random(Rs^1,Rs^{dim Rs-2:-1});
       pts=decompose (f+H);
       pts1=select(pts,pt-> degree pt==1 and dim pt ==1);
       ok=( #pts1>0); 
       if ok then (pt=saturate(sub(pts1_0,R)+I);ok==(degree pt==1 and dim pt==0));
     not ok) do (trial=trial+1);
     pt)
     
TEST ///
     p=10007,kk=ZZ/p 
     R=kk[x_0..x_2]
     I=ideal(random(4,R)); 
     time randomKRationalPoint(I)
     R=kk[x_0..x_4]
     I=minors(3,random(R^5,R^{3:-1}));
     codim I
     time randomKRationalPoint(I)     
///



artinianReduction=method()
artinianReduction(Ideal):= I -> (
     T:=ring I;
     kk:=coefficientRing T;
     T1:=kk[apply(codim I,j-> T_j)];
     I1:=substitute(I,T1);
     if not (dim I1==0 and degree I==degree I1) 
     then error "the last dim I variables do not form a regular sequence";
     (T1,I1))

expectedSyzygies=method(TypicalValue=>BettiTally)

expectedSyzygies(ZZ,List) := (n,H) -> (
     -- n number of variables, 
     -- H list incoding the Hilbert function of a finite length module 
     -- with smallest degree generator in degree 0 
     -- the answer is a reasonable guess, if the Hilbert numerator has n sign 
     -- changes in the coefficients     
     t := symbol t;
     T := QQ[t];
     hilbertNumerator := sum(#H,i->H_i*t^i)*(1-t)^n;
     d := (degree hilbertNumerator)_0;
     a:=1;sign:=1;homodeg:=0;
     bT := sum(0..d,i->(a=lift(sub(contract(t^i,hilbertNumerator),t=>0),ZZ);
	 if  a!=0 then ((if (a*sign) < 0 then (sign=-sign;homodeg=homodeg+1);
	       new BettiTally from { (homodeg,{i},i) => (sign*a) }))
	       else new BettiTally from {(0,{0},0) => 0}));
     bT)
 

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



beginDocumentation()

doc ///
  Key
    extrasForTheKernel
  Headline
    constructions of prime fields and artinian reductions     
  Description
    Text

      {\it Version 0.1.}      

      {\bf Overview:}
         A collection of a few functions that will be use ful in many cases.
	 
     
      
      

      {\bf Setup:}

      This package requires Macaulay2 version 1.4 or newer.

      Install this @TO Package@ by doing

      @TO installPackage@("extrasForTheKernel")

      --{\bf Examples:}
      
///
doc ///
  Key
    nextPrime
    (nextPrime,ZZ)
  Headline
    Compute the smallest prime larger or equal n.
  Usage
    nextPrime(n)     
  Inputs
    n: ZZ
  Outputs
    p: ZZ
        the smallest prime $p \ge n$
  Description
     Text  
     Example
       p=nextPrime(10000)
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
    randomKRationalPoint
    (randomKRationalPoint,Ideal)
  Headline
    Pick a random K rational point on the scheme X defined by I
  Usage
    randomKRationalPoint(I)    
  Inputs
    I: Ideal
       in a polynomial ring over a finite ground field K
  Outputs
     : Ideal
       of a K-rational point on V(I)
  Description
     Text
        If X has codimension 1, then we intersect X with a randomly choosen
     	line, and hope that the decomposition of the the intersection contains a 
     	K-rational point. This happens in about 61% of the cases. So a probabilistic 
     	approach will work.
	
     	For higher codimension we first project X birationally onto a 
     	hypersurface Y, and find a point on Y. Then we take the preimage of this point.
     Example
       p=nextPrime(random(2*10^4))
       kk=ZZ/p;R=kk[x_0..x_3];
       I=minors(4,random(R^5,R^{4:-1}));
       codim I, degree I
       time randomKRationalPoint(I)
       R=kk[x_0..x_5]; 
       I=minors(3,random(R^5,R^{3:-1})); 
       codim I, degree I
       time randomKRationalPoint(I)

     Text
        That about 61 % of the intersection contain a K-rational point can seen experimentally
     Example
        p=10007,kk=ZZ/p,R=kk[x_0..x_2]
        I=ideal random(5,R); 
        time (#select(apply(100,i->(degs=apply(decompose(I+ideal random(1,R)),c->degree c); 
		  #select(degs,d->d==1))),n->n>0))*1.0
        I=ideal random(10,R); 
        time (#select(apply(100,i->(degs=apply(decompose(I+ideal random(1,R)),c->degree c); 
		  #select(degs,d->d==1))),n->n>0))*1.0
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
    compute all Koszul maps of total degree p  for an artinian ideal I
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
       setRandomSeed("ok")
       R=ZZ/101[x_0..x_4];
       I = ideal random(R^1,R^{7:-2});
       assert(dim I==0)
       H=apply(3,i->hilbertFunction(i,I))
       expectedSyzygies(5,H)
       cp=criticalKoszulDegrees(I)
       (L,N)=koszulMaps(I,cp_0);L
       apply(#N,j->betti N_j)
       rank coker N_0,rank (ker N_0/image N_1),rank ker N_1
       betti res I
       (L,N)=koszulMaps(I,2);L
       apply(#N,j->betti N_j)
       rank coker N_0,rank (ker N_0/image N_1),rank ker N_1
///

doc ///
  Key
    criticalKoszulDegrees
    (criticalKoszulDegrees,Ideal)
  Headline
    compute all d with $\sum_{p+q=d} (-1)^q dim K_{p,q}(S/I)==0$ for an artinian ideal I
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
       setRandomSeed("ok")
       R=ZZ/101[x_0..x_4];
       I = ideal random(R^1,R^{7:-2});
       assert(dim I==0)
       H=apply(3,i->hilbertFunction(i,I))
       expectedSyzygies(5,H)
       cp=criticalKoszulDegrees(I)
///

doc ///
  Key
    expectedSyzygies
    (expectedSyzygies,ZZ,List)
  Headline
    compute the expected Betti numbers of an artinian module
  Usage
    expectedSyzygies(n,H)
  Inputs
    n: ZZ
       the number of variables
    H: List
      the Hilbert function given as a list
  Outputs
     : BettiTally        
  Description
     Text
       Compute the expected Betti numbers of an graded artinian module with smallest degree generator
       in degree 0 from its Hilbert function over a standard graded polynomial ring in n variables.
       Method: sign changes in the Hilbert numerator 
       $$(1-t)^n  \sum_{\ i\ge 0} H_i t^i= \sum_{i=0}^n \sum_j \ \beta_{ij} t^j$$
     Example
       expectedSyzygies(5,{1,5,8})
       
///


end;
------------------------------------
--- Left overs from previous versions
-------------------------------------
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
--- for randomKRational
     Text
        That about 61 % of the intersection contain a K-rational point can ssen experimentally
     Example
        p=10007,kk=ZZ/p,R=kk[x_0..x_2]
        I=ideal random(5,R); 
        time (#select(apply(100,i->(degs=apply(decompose(I+ideal random(1,R)),c->degree c); 
		  #select(degs,d->d==1))),n->n>0))*1.0
        I=ideal random(10,R); 
        time (#select(apply(100,i->(degs=apply(decompose(I+ideal random(1,R)),c->degree c); 
		  #select(degs,d->d==1))),n->n>0))*1.0
     	time randomKRationalPoint(I)     

--------------------------
--- end of left overs
-------------------------
     
      Example	 
         kk=nextPrime(random(2*10^4))
         R=kk[x_0..x_3]
	 I=minors(4,random(R^5,R^{4:-1})
	 codim I, degree I
	 time randomKRationalPoint(I)
	 R=kk[x_0..x_5] 
	 I=minors(3,R^5,R^{3:-1}) 
	 codim I, degree I
	 time randomKrationalPoint(I)



 p=10007,kk=ZZ/p,R=kk[x_0..x_2]
         I=ideal random(5,R); 
         time (#select(apply(100,i->(degs=apply(decompose(I+ideal random(1,R)),c->degree c); 
		  #select(degs,d->d==1))),n->n>0))*1.0
         I=ideal random(10,R); 
         time (#select(apply(100,i->(degs=apply(decompose(I+ideal random(1,R)),c->degree c); 
		  #select(degs,d->d==1))),n->n>0))*1.0
     	 time randomKrationalPoint(I)
///
      
restart
uninstallPackage("extrasForTheKernel")
installPackage("extrasForTheKernel",RerunExamples=>true,RemakeAllDocumentation=>true);
viewHelp "extrasForTheKernel"


