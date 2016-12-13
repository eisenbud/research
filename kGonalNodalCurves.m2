newPackage(
	"kGonalNodalCurves",
Version=>"0.2",
Date=> "09, 2016",
Authors=>{{Name => "Christian Bopp",
		   Email =>"bopp@math.uni-sb.de",
		   HomePage =>"http://www.math.uni-sb.de"}
						},
Headline=> "construction of rational k-gonal g-nodal canonical curves",
DebuggingMode=>true
	)
   
export{"getFieldAndRing", 
       "getFactors", 
       "getCoordinates", 
       "pickGoodPoints", 
       "listOfFactors", 
       "linFactorsToQuadric",
       "getSections", 
       "sectionsFromPoints",
       "idealOfNodalCurve", 
       "canonicalMultipliers",
       "idealOfNodalCurveByPoints", 
       "criticalBettiNumberWithoutArtinanReduction",
       "criticalBettiNumber",
       "criticalKoszulMap",
       "sparseKoszulMatrix",
       "getBackMatrix",
       "lineBundleFromPointsAndMultipliers",
       --H0KrD,
       "scrollType",
       "artinianReduction"}

-- Update from Version 0.1 to 0.2
-- no longer depends on the Package ExtrasForTheKernel       
       

--needsPackage("extrasForTheKernel") -- no longer needed
--------------------------------------------------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------------------------------------------------

-- constructs field with small characteristic
-- and coord.ring of PP^1 over this field
getFieldAndRing=method()
getFieldAndRing(ZZ):=(n)->( 
     x:= getSymbol "x";  
     p:=nextPrime(n+1); 
     kk:=ZZ/p;
     S:=kk[x_0,x_1];
     p,kk,S
     );
--------------------------------
-- method taken from "extrasForTheKernel"
artinianReduction=method()
artinianReduction(Ideal):= I -> (
     T:=ring I;
     kk:=coefficientRing T;
     T1:=kk[apply(codim I,j-> T_j)];
     I1:=substitute(I,T1);
     if not (dim I1==0 and degree I==degree I1) 
     then error "the last dim I variables do not form a regular sequence";
     (T1,I1))
 
 ---------------------------------
-- method taken from "extrasForTheKernel"
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
---------------------------------

-- computes list L1 of linearfactors of a polynomial 
-- and list L2 of quadric factors of a polynomial and gives back L1,L2
getFactors=method()
getFactors(RingElement):=(f)->(
     S:=ring f;
     L1:={};
     L2:={};
     facs:=apply(toList(factor f), fac->fac#0) ;
     if (f==0_S) then (L1,L2)=({},{}) else      
     (L1,L2)=(select(facs,fac->degree fac=={1}),select(facs, fac->degree fac=={2}) );--List of linear and quadratic factors
     L1,L2
     );

---------------------------------

 -- computes the vanishing loci of a linear polynomial in two variables
getCoordinates=method()
getCoordinates(RingElement):=(l)->( 
     S:=ring l;
     if rank source (coefficients(l))#0==2 then
     matrix{{-(coefficients l)_1_(1,0), (coefficients l)_1_(0,0)}}
     else if sub((coefficients(l))#0,S) - map(S^1,S^1,(entries vars S)_0#0)==0 then matrix{{0,1}}
     else if sub((coefficients(l))#0,S) - map(S^1,S^1,(entries vars S)_0#1)==0 then matrix {{1,0}}	  
     );

---------------------------------

-- We build a list L containing at least two linear or one quadric factor of det(f|pt)
-- for a morphism f:PP^1-->PP^1 of degree d and g distinct points pt in PP^1
listOfFactors=method()
listOfFactors(ZZ,ZZ,ZZ):=(k,g,n)->(
      (p,kk,S):=getFieldAndRing(n);
      --L:={};
      (L,L1,L2):=({},{},{}); 
      pts:=random(apply(p,i-> matrix{{i,1}})|{matrix{{1,0}}});
   while (#L<g or #(unique flatten L)< #(flatten L)) do (  
	 (L,L1,L2)=({},{},{}); 
	     f:=random(S^1, S^{2:-k});
	     j:=0;
	 while (#L<g and j<p)  do ( if #(L1=(getFactors(sub(det(f||sub(pts_j,S)),S)))#0)>=2 then L= L|{L1}
		               else if #(L2=(getFactors(sub(det(f||sub(pts_j,S)),S)))#1)>=1 then L=L|{L2};
			           j=j+1;  
				   );
	     	       	    	      	   	     	  );
     	       	    	L
	       );
		   
---------------------------------

-- we proceed in the same way as in the function "listOfFactors" but only save linear factors 
-- we compute the 2g points (P_i,Q_i) that will glue together to a node as the vanishing loci of the linear factors
-- and give them back together with the morphism f and a list {a_i,i=1...g} where (a_i,1) are the multipliers corresp. to the bundle
pickGoodPoints=method()
pickGoodPoints(ZZ,ZZ,ZZ):=(k,g,n)->(
      (p,kk,S):=getFieldAndRing(n);
      --L:={};
      (L,L1):=({},{});
      multL:={};
      pts:=random(apply(p,i-> matrix{{i,1}})|{matrix{{1,0}}});
   while (#L<g or #(unique flatten L)< #(flatten L)) do (  
	 (L,L1)=({},{}); 
	     f:=random(S^1, S^{2:-k});
	     j:=0;
	 while (#L<g and j<p)  do ( if #(L1=(getFactors(sub(det(f||sub(pts_j,S)),S)))#0)>=2 then L= L|{L1};	    
			           j=j+1;  
				   );
			                              );
     	  P:=transpose matrix apply(L,l->(flatten entries getCoordinates l_0));
          Q:=transpose matrix apply(L,l->(flatten entries getCoordinates l_1));	
	  multL=apply(g,i->sub(sub(f_(0,0),transpose(P_{i})),kk)/sub(sub(f_(0,0),transpose(Q_{i})),kk));				 
     	  (P,Q,multL,f) 	    	
	    );		   

---------------------------------

-- computes the canonical multipliers
-- this function is identic to one from the M2 package "NodalCurves.m2"
canonicalMultipliers=method()
canonicalMultipliers(Matrix,Matrix) := (P,Q) -> (
     -- P and  Q two 2xg matrices representing 2g distinct points of P^1
     S:=ring P;
     if dim S != 2 then error "not a Polynomialring in two variables";
     g:= numcols P; 
     quadrics := apply(g, i->(det(P_{i}|(transpose vars S)))*(det(Q_{i}|(transpose vars S))));
     sections := (apply(g, i -> product(g, j-> if i == j then 1_S else quadrics_j)));
     -- a basis of the canonical series as subseries of S_{2g-2} of the nodal curve
     A := transpose matrix(apply(g, i ->{sub(sections_i, transpose P_{i}), sub(sections_i, transpose Q_{i})}));
     A);  

---------------------------------

-- constr quadric from >=2 linear factors 
-- needed to compute a matrix representing the canonical embedding
linFactorsToQuadric=method()
linFactorsToQuadric(List,ZZ):=(l,n)->(-- constr quadric from >=2 linear factors --> see package NodalCurves.m2: the function canonicalMultipliers for details
     (p,kk,S):=getFieldAndRing(n);
     lh:=random(l);
     (P,Q):=(sub(getCoordinates(lh_0),S),sub(getCoordinates(lh_1),S));
     quad:=(det(P||(vars S)))*(det(Q||(vars S)));
     quad 
     ); 

---------------------------------

-- We construct the sections that define the canonical embedding
getSections=method()
getSections(ZZ,ZZ,ZZ):=(k,g,n)->(
     (p,kk,S):=getFieldAndRing(n);    
     	  quadrics:={};
	  M:=0;
	  L:=listOfFactors(k,g,n);
     	  for i from 0 to (#L-1) do (
	  a:=(degree((L_i)_0))_0;
	  if a==1 then    quadrics=quadrics|{linFactorsToQuadric(L_i,n)}
	  else      quadrics=quadrics|{(L_i)_(random(#L_i))}     );
          s:=matrix {apply(g, i -> product(g, j-> if i == j then 1_S else sub(quadrics_j,S)))};    
       	  while (M=random(S^{g:0},S^{g:0}); det M==0) do ();
	  s2:=s*M;--get more general sections -> better chance, that the artinian reduction works
	  assert(ideal s==ideal s2);
	  s2
     	  );       

--------------------------------- 
-- computes the ideal of a nodal curve over field with small characteristics
idealOfNodalCurve=method()
idealOfNodalCurve(ZZ,ZZ,ZZ):=(k,g,n)-> (
      (p,kk,S):=getFieldAndRing(n);
      t:=getSymbol "t";  
      T:=kk[t_0..t_(g-1)];
      s:=sub(getSections(k,g,n),S);  
      I:=ideal mingens ker map(S,T,s)
      );      
 
--------------------------------

-- computes the matrix s of sections defining the canonical embedding from the 2g points P_i,Q_i
sectionsFromPoints=method()
sectionsFromPoints(Sequence):=(PQ)->(
     (P,Q):=(PQ_0,PQ_1);
     M:=0;
     S:=ring P;
     if dim S != 2 then error "not a Polynomialring in two variables";
     g:= numcols P; 
     quadrics := apply(g, i->(det(P_{i}|(transpose vars S)))*(det(Q_{i}|(transpose vars S))));
     sections :=matrix {(apply(g, i -> product(g, j-> if i == j then 1_S else quadrics_j)))};
     while (M=random(S^{g:0},S^{g:0}); det M==0) do ();
     s:=sections*M
     );

sectionsFromPoints(Matrix,Matrix):=(P,Q)->(
     M:=0;
     S:=ring P;
     if dim S != 2 then error "not a Polynomialring in two variables";
     g:= numcols P; 
     quadrics := apply(g, i->(det(P_{i}|(transpose vars S)))*(det(Q_{i}|(transpose vars S))));
     sections :=matrix {(apply(g, i -> product(g, j-> if i == j then 1_S else quadrics_j)))};
     while (M=random(S^{g:0},S^{g:0}); det M==0) do ();
     s:=sections*M
     );

--------------------------------

idealOfNodalCurveByPoints=method()
idealOfNodalCurveByPoints(Matrix,Matrix,ZZ):=(P,Q,n)->(
     g:=numcols P;
     (p,kk,S):=getFieldAndRing(n);
     t:=symbol t;
     T:=kk[t_0..t_(g-1)];     
   --  PQ:=pickGoodPoints(d,g,n);
   --  s:=sectionsFromPoints(PQ);
     s:=sub(sectionsFromPoints(P,Q),S);
     assert(rank source s==g);
     I:=ideal mingens ker map(S,T,s);
     I 
     );
     
--------------------------------

-- computes critical betti number with artinian reduction
criticalBettiNumber=method()
criticalBettiNumber(Ideal):=(I)->(
     T:=ring I;  
     g:=rank source vars T;
     m:=ceiling((g-1)/2);
     (T1,I1):=artinianReduction(I);   
     M2:=koszulMap(I1,m,1);
    rank(ker M2)- binomial(g-2,m+1)
    );

criticalBettiNumber(ZZ,ZZ,ZZ):=(k,g,n)->(
     (p,kk,S):=getFieldAndRing(n);
     t:=symbol t;
     T:=kk[t_0..t_(g-1)];     
     m:=ceiling((g-1)/2);
     s:=sub(getSections(k,g,n),S);
     I:=ideal mingens ker map(S,T,s);
     (T1,I1):=artinianReduction(I);
     M2:=koszulMap(I1,m,1);
    rank(ker M2)- binomial(g-2,m+1)
    );

--------------------------------

-- computes the critical bettinumber via Koszulcohomology, 
-- but without artinian reduction
 criticalBettiNumberWithoutArtinanReduction=method()
 criticalBettiNumberWithoutArtinanReduction(Ideal):=(I)->(
     T:=ring I;
     g:=rank source vars T;   
     m:=ceiling((g-1)/2);
     M2:=koszulMap(I,m,1);
     rank(ker M2)- binomial(g,m+1)
);

 criticalBettiNumberWithoutArtinanReduction(ZZ,ZZ,ZZ):=(k,g,n)->(
     (p,kk,S):=getFieldAndRing(n);
     t:=symbol t;
     T:=kk[t_0..t_(g-1)];     
     m:=ceiling((g-1)/2);
     s:=sub(getSections(k,g,n),S);
     I:=ideal mingens ker map(S,T,s);
     M2:=koszulMap(I,m,1);
     rank(ker M2)- binomial(g,m+1)
); 

-------------------------------

-- computes the koszulmap whose rank determines the critical Betti number
-- uses artinian reduction
criticalKoszulMap=method()
criticalKoszulMap(Ideal):=(I)->(
     T:=ring I;
     g:=rank source vars T;   
     m:=ceiling((g-1)/2);
     (T1,I1):=artinianReduction(I);
     M:=koszulMap(I1,m,1);
     M
     );

criticalKoszulMap(ZZ,ZZ,ZZ):=(k,g,n)->(
     (p,kk,S):=getFieldAndRing(n);
     t:=symbol t;
     T:=kk[t_0..t_(g-1)];     
     m:=ceiling((g-1)/2);
     s:=sub(getSections(k,g,n),S);
     I:=ideal mingens ker map(S,T,transpose s);
     (T1,I1):=artinianReduction(I);
     M:=koszulMap(I1,m,1);
     M
     );

------------------------------------

-- computes a list containing the characteristic of the ground field, the size of the critical koszulmap 
-- and a list of the nonzero entries and the position of those
-- function is based on a function in the M2 package "NodalCurves.m2"
sparseKoszulMatrix=method()
sparseKoszulMatrix(Ideal):=(I)->(
     T:= ring I;
     kk:=coefficientRing(T);
     g:= rank source vars T;
     m:=ceiling((g-1)/2);
     (T1,I1):=artinianReduction(I);
     B:=T1/I1;
     B2:=basis(2,B);
     lT:=(leadTerm  mingens ideal(B2));
     tis:=vars T1;
     B1:=basis(1,B);
     theList:=apply(rank source tis,i->(sub(contract(transpose lT,tis_(0,i)*B1),kk)));
     -- this List defines the multiplication B1->B2 defined by multiplying by all the t_i's
     -- i.e we take a basis multiply it with the t_i's and get the representation in terms of a basis of B2
     indexList:=toList(0..g-3);
     gm:=subsets(indexList,m);
     gm1:=subsets(indexList,m-1);
     alpha:=gm_0;beta:=gm1_0;pos:=0;
     LL:=flatten apply(#gm,jj->(alpha=gm_jj;
     	       	         flatten apply(m,k->(beta=delete(alpha_k,alpha);
			             pos=position(gm1,b->b==beta);
			        flatten apply(g-2, i->apply(g-2,j->((g-2)*pos+i,(g-2)*jj+j, (-1)^k*theList_(alpha_k)_(i,j))
					                       )
					         ))
			  	     ))
		      );
    (char(kk),(g-2)*binomial(g-2,m-1),(g-2)*binomial(g-2,m),LL)
    );

--------------------------

-- reconstructs the matrix from as list of the type given back by the function "sparseKoszulMatrix"
getBackMatrix=method()
getBackMatrix(ZZ,ZZ,ZZ,List):=(characteristic, rows, cols, LL)->(
     kk:=ZZ/characteristic;
     mutMat:=mutableMatrix(kk,rows,cols,Dense=>false);
      for i from 0 to (#LL-1) do mutMat_((LL_i)_0,(LL_i)_1)=(LL_i)_2;
     G:=matrix mutMat;
     G
     );

------------------------

-- computes the global sections of a linebundle of degree d 
-- from the normalized multipliers (i.e. multipliers of the form (a_i,1)) 
-- and points
lineBundleFromPointsAndMultipliers=method()
lineBundleFromPointsAndMultipliers(List,Matrix,Matrix,ZZ):=(ms,P,Q,k)->(
     S:=ring P;
     B:=flatten entries basis(k,S);
     M:=matrix apply(#ms,i->apply(k+1,j->sub(B_j,transpose(P_{i}))-ms_i*sub(B_j,transpose(Q_{i}))));
     basis(k,S)*syz M
     );

------------------------

-- computes H^0(OO_C,K-rD)
-- takes list PQ of points P and Q since M2 can't handle more 
-- than 4 arguments in a function
H0KrD=method()
H0KrD(Sequence,List,ZZ,ZZ):=(PQ,multL,r,k)->(
     (P,Q):=(PQ_0,PQ_1);
     g:=numcols P;
     kk:=coefficientRing (ring P);
     multK0:=sub(canonicalMultipliers(P,Q),kk);
     multK:=apply(g,i->multK0_(0,i)/multK0_(1,i));
     multKrD:=apply(g,i->multK_i/(multL_i^r));
     lineBundleFromPointsAndMultipliers(multKrD,P,Q,2*g-2-r*k)
     );
undocumented H0KrD

------------------------

-- computes the type of the scroll on which a d-gonal g-nodal curve lies
-- see Schreyer "Syzygies of canonical curves and special linear series, Math.Ann 1986" for details
scrollType=method()
scrollType(ZZ,ZZ,ZZ):=(k,g,n)->(
     eDual:={}; -- the dual partition
     (P,Q,multL,f):=pickGoodPoints(k,g,n);
     PQ:=(P,Q);
    -- for i from 0 to (d-2) do (
    --     Dual0:=rank source H0KrD(P,Q,multL,i) - rank source H0KrD(P,Q,multL,i+1);
    --     if Dual0<=0 then break else (eDual=eDual|{Dual0}));
    j:=0;
    while rank source H0KrD(PQ,multL,j,k)>0 do(j=j+1);
    eDual=apply(j,i->rank source H0KrD(PQ,multL,i,k) - rank source H0KrD(PQ,multL,i+1,k));
     e:=apply(k-1,i->#select(eDual,e0->e0>=i+1)-1);--the type of the scroll
     e
     );
 
----------------------------------------------------------------------

beginDocumentation()

document { 
  Key => kGonalNodalCurves,
  Headline => "consrtuction of rational k-gonal g-nodal canonical curves",
  "We construct two sets of g points in PP^1, represented by two 2xg matrices P,
   and Q in such a way that the curve constructed by gluing this points to nodes
   as implemented in the 
       the Macaulay2 package ", 
	 HREF("http://www.math.uni-sb.de/ag/schreyer/home/NodalCurves.m2","NodalCurves") ,
	 " gives a nodal curve that carries a g^1_k.",	 	 
   --"We proceed as follows:",
   --PARA{},
   --"Step 1. We search a morphism","f:PP^1 ->PP^1 ", "such that the",
    --"2x2 ", "determinan t",
    --"det(f|pt_i) ", "has at least 2 linear factors for g distinct points ",
    --"pt_i", "in an affine chart.",
   --PARA{},   
   --"Step 2. We compute 2g points", TT"P_i, Q_i", "as the vanishing loci of these
   --forms. ,
   PARA{},
   "The variety swept out by a g^1_k on a canonical curve is a (k-1) dimensional
   rational normal scroll X ", "We want to check whether the Betti numbers ",
   TT "beta_{m+c,m+c+1}(C)", "coincide with those of the scroll for c>=0 and
   m=ceiling((g-1)/2). 
   This package also provides several functions which can be handy for the computation
   of the critical Betti number ", TT "beta_{m,m+1}(C)", "using Koszul cohomolgy.",
   "See ", HREF("http://projecteuclid.org/DPubS/Repository/1.0/Disseminate?view=body&id=pdf_1&handle=euclid.jdg/1214438426","Koszul Cohomology and the Geometry of Projective Varieties"),
   " for a good survey on the topic.",	 
   PARA{},
   SUBSECTION "Construction of rational d-gonal g-nodal canonical curves",  
   UL{   TO getFieldAndRing,
	 TO getFactors,
	 TO getCoordinates,
         TO pickGoodPoints,
         TO listOfFactors,
	 TO linFactorsToQuadric,
	 TO getSections,
	 TO sectionsFromPoints,
	 TO canonicalMultipliers,
	 TO lineBundleFromPointsAndMultipliers,
	 TO idealOfNodalCurve,
	 TO idealOfNodalCurveByPoints,
	 TO scrollType
      },
   SUBSECTION "Computation of the critical Betti number",
   UL{
         TO criticalKoszulMap,
         TO criticalBettiNumber,
	 TO criticalBettiNumberWithoutArtinanReduction,
	 TO sparseKoszulMatrix,
	 TO getBackMatrix
      },
  Caveat => {"This package requires Macaulay2 Version 1.9 or newer "} 
   }

doc ///
  Key 
    getFieldAndRing
    (getFieldAndRing,ZZ) 
  Headline 
    computes a prime number p>=n, the field kk=ZZ/p and the coordinate Ring S of PP^1(kk)
  Usage
    (p,kk,S)=getFieldAndRing(n)
  Inputs
    n: ZZ      
  Outputs
    p: ZZ
       prime number $p>=n$
    kk: QuotientRing
       the quotientring ZZ/p
    S: PolynomialRing
       the coordinatering kk[x_0,x_1] of PP^1(kk)      
  Description
     Text
       computes a prime number $p\geq n$, the field kk=ZZ/p, and 
       the coordinate Ring S of PP^1(kk)
///  

doc ///
  Key 
    getFactors
    (getFactors,RingElement) 
  Headline 
    computes linear and quadratic factors of a polynomial
  Usage
    (L1,L2)=getFactors(f)
  Inputs
    f: RingElement  
  Outputs
    L1: List
       containing the linear factors of f
    L2: List
       containing the quadric factors of f        
  Description
     Text
       computes a list L1 of linearfactors and a list L2 of quadric factors 
       of a polynomial f.  
       
///

doc ///
  Key 
    getCoordinates
    (getCoordinates,RingElement) 
  Headline 
    computes vanishing loci of a linear polynomial in two variables
  Usage
    p=getCoordinates(f)
  Inputs
    f: RingElement 
       linear polynomial in kk[x_0,x_1]
  Outputs
    p: Matrix
       representing a point in PP^1      
  Description
     Text
       computes the point corresponding to a linearform $f\ \in$ kk[x_0,x_1].     
       
///

doc ///
  Key 
   listOfFactors
    (listOfFactors,ZZ,ZZ,ZZ) 
  Headline 
    finds a map f: S^2(-k)->S such that det(f|pt) factors factors for sufficiently many points pt in PP^1
  Usage 
    L=listOfFactors(k,g,n)
  Inputs
    k: ZZ
       the degree of the special pencil
    g: ZZ
       the genus of the curve we want to construct
    n: ZZ
       defining the characteristic of our ground field (see @ TO getFieldAndRing @ for details)       
  Outputs
    L: List
       with g entries, each entrie consists of the linear and quadratic factors of f|pt for a pt in PP^1      
  Description
     Text
       Searches a random map $f:S^2(-k)\to S$ such that $det(f|pt_i)$ has
       at least two linear or one quadratic factor for g distinct points $pt_i$
       in an affine chart of PP^1. Afterwards these factors are saved to a list. 
    
     Example
         (k,g,n)=(5,8,7);
         L=listOfFactors(k,g,n)
	 #L==g        
       
///

doc ///
  Key 
   getSections
    (getSections,ZZ,ZZ,ZZ) 
  Headline 
    computes a matrix defining the canonical embedding
  Usage 
    s=getSections(k,g,n)
  Inputs
    k: ZZ
       the degree of the special pencil
    g: ZZ
       the genus of the curve we want to construct
    n: ZZ
       defining the characteristic of our ground field (see @ TO getFieldAndRing @ for details) 
  Outputs
    s: Matrix
       with g entries. Each entry is a basis element of $H^0(C,\omega_C)$   
  Description
     Text
       Constructs a matrix s of sections that defines an embedding PP^1->PP^{g-1} 
       such that the image is a k-gonal g-nodal canonical curve.
       The construction of the sections is based on the construction  implemented in the 
       M2 package @ HREF("http://www.math.uni-sb.de/ag/schreyer/home/NodalCurves.m2","NodalCurves") @.
       
       Step 1. We search $f:S^2(-k)\to S$ such that $det(f|pt_i)$ has
       at least two linear or one quadratic factor for g distinct points $pt_i$
       in an affine chart of PP^1. This part is done by the function
       @TO listOfFactors@.
       
       Step 2.We build g quadrics q_i: if  $det(f|pt_i)$ has two linear factors
       then we commpute the two points P_i and Q_i as the vanishing loci of
       the linear factors and define $q_i\ :=det(P_i\ |\ (x_0,x_1)^t)\ *\ det(Q_i\ |\ (x_0,x_1)^t).$
       If $det(f|pt_i)$ already has a quadratic factor we can definie $q_i$ to
       be this factor.
       
       Step 3. We compute a basis of $H^0(C,\omega_C)$ by
       $\{s_i\ :=\prod^g_{j\neq i,j=1}q_i\ |\ i=1,...,g \}$ and multiply the
       matrix s=(s_1,...,s_g) with a general matrix $M\in GL(g,kk)$ to 
       obtain more general sections. 
       
     Example
         (k,g,n)=(4,8,100);
	 (p,kk,S)=getFieldAndRing(n);
         time s=sub(getSections(k,g,n),S);
	 T=kk[t_0..t_(g-1)];
	 time I=ideal mingens ker map(S,T,s);
	 time betti res I        
  SeeAlso
    sectionsFromPoints       
///

doc ///
  Key 
    idealOfNodalCurveByPoints
    (idealOfNodalCurveByPoints,Matrix,Matrix,ZZ) 
  Headline 
    computes ideal of a canonical nodal curve constructed from 2g points
  Usage
    I=nodalCurveByPoints(P,Q)
  Inputs
    P: Matrix
       representing g points of PP^1(kk)
    Q: Matrix
       representing another g points of PP^1(kk)   
    n: ZZ
       defining the characteristic of the ground field (see @ TO getFieldAndRing @ for details)     
  Outputs
    I: Ideal
       the ideal of the canonical curve 
  Description
     Text
       Constructs a rational k-gonal g-nodal canonical curve as follows:
       
       Step 1. Computes a matrix s representing the canonical series of the singular curves with the
       function @ TO sectionsFromPoints @ from 2g points P_i,Q_i.        
                    
       Step 2. Computes the homogeneous ideal I of the curve as the kernel of the
       map $s:T=kk[t_0,...,t_{g-1}]\to S=kk[x_0,x_1]$.
       
       The construction method is similar to the method implemented in the M2 package
        @ HREF("http://www.math.uni-sb.de/ag/schreyer/home/NodalCurves.m2","NodalCurves") @.   
       
     Example
         (k,g,n)=(4,8,1000);
         time (P,Q,multL,f)=pickGoodPoints(k,g,n);
	 time I=idealOfNodalCurveByPoints(P,Q,n);
	 time betti res I         

  SeeAlso
    idealOfNodalCurve
    sectionsFromPoints         
///

doc ///
  Key 
   idealOfNodalCurve
    (idealOfNodalCurve,ZZ,ZZ,ZZ) 
  Headline 
    computes the ideal I of a k-gonal g-nodal canonical curve.
  Usage 
    I=idealOfNodalCurve(k,g,n)
  Inputs
    k: ZZ
       the degree of the  d-gonal map we want to construct.
    g: ZZ
       the genus of the curve we want to construct.
    n: ZZ
       defining the characteristic of our ground field (see @ TO getFieldAndRing @ for details) 
  Outputs
    I: Ideal
       the ideal I of the canonical nodal curve.      
  Description
     Text
       Constructs the ideal of a rational k-gonal g-nodal canonical curve.
       
       Step 1: computes the matrix s of sections that defines the canonical embedding
       with the function @ TO getSections @.
       
       Step 2: computes I as the kernel of the map $s: kk[x_0,x_1]->kk[t_0,..,t_{g-1}]$.
    
     Example
         (k,g,n)=(4,8,1000);
         time I=idealOfNodalCurve(k,g,n);
	 time betti res I      
  
  SeeAlso
    getSections
    idealOfNodalCurveByPoints       
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
       A: Matrix
	  A of multipliers          
  Description
     Text
       This function is identic to the function "canonicalMultipliers" from
       the M2 package  @ HREF("http://www.math.uni-sb.de/ag/schreyer/home/NodalCurves.m2","NodalCurves") @. 
       Given g pairs of points P_i, Q_i, on PP^1 
       computes the canonical series of the corresponding nodal curve of 
       genus g and determines the g ratios A_i of the glueing data for the canonical bundle
       (note that A_i depends on the choice of the
       homogeneous coordinates of the point P_i and  Q_i).
  
       Step 1.We compute g quadrics q_i 
       $q_i\ :=det(P_i\ |\ (x_0,x_1)^t)\ *\ det(Q_i\ |\ (x_0,x_1)^t).$ and
       a basis of $H^0(C,\omega_C)$ by
       $\{s_i\ :=\prod^g_{j\neq i,j=1}q_i\ |\ i=1,...,g \}$.
       
       Step 2. We compute the multipliers
       $a_i=s_i(P_i)$ and $b_i=s_i(Q_i)$
///

doc ///
  Key  
    linFactorsToQuadric
    (linFactorsToQuadric,  List, ZZ)
  Headline 
    computes quadrics needed to construct the matrix defining the canonical embedding 
  Usage
    linFactorsToQuadric(l,n)
  Inputs
       l: List
          containg two linear forms
       n: Matrix
          defining the characteristic of the groundfield. See @ TO getFieldAndRing @ for details.
  Outputs
       q : PolynomialRing
	  a quadric needed to construct the sections defining the canonical embedding          
  Description
     Text
       Computes a quadric for each pair of linear factors obtained by the function 
       @ TO listOfFactors@. The quadric is defined as follows: 
       We commpute the two points P_i and Q_i as the vanishing loci of
       the linear forms and define $q_i\ :=det(P_i\ |\ (x_0,x_1)^t)\ *\ det(Q_i\ |\ (x_0,x_1)^t).$
       
  SeeAlso
    getSections
    listOfFactors     
///

doc ///
  Key  
    scrollType
    (scrollType, ZZ, ZZ,ZZ)
  Headline 
    determines the type of the scroll
  Usage
    scrollType(k,g,n)
  Inputs
       k: ZZ
          degree of the line bundle on the curve C
       g: ZZ
          genus of C
       n: ZZ
          defining the characteristic of the ground field (see @ TO getFieldAndRing @ for details) 	  
  Outputs
       e : List
	  specifying the type of the scroll swept out by the g^1_k on C          
  Description
     Text
       Constructs a special pencil on a g-nodal canonical curve and
       computes the type of the scroll swept out by the special pencil. The
       method used for the computation is based on the article
       @HREF("http://link.springer.com/article/10.1007%2FBF01458587?LI=true","Syzygies of Canonical Curves and Special Linear Series")@.
       
     Example
        (k,g,n)=(5,13,1000)
        time scrollType(k,g,n)
	       
///

doc ///
  Key  
    lineBundleFromPointsAndMultipliers
    (lineBundleFromPointsAndMultipliers, List, Matrix, Matrix, ZZ)
  Headline 
    computes basis of a line bundle from the 2g points P_i, Q_i and the multipliers 
  Usage
    lineBundleFromPointsAndMultipliers(multL,P,Q,k)
  Inputs
       multL: List
          containing the normalized multipliers a_i (normalized means that b_i=1)
       P: Matrix
          coordinate matrix of g points in PP^1
       Q: Matrix
          coordinate matrix of g points in PP^1
       k: ZZ
          defining the degree of the line bundle	  	  
  Outputs
       f : Matrix
	  a basis of sections of the line bundle defined by the points 
	  P_i, Q_i and the multipliers          
  Description
     Text
       If C is a g-nodal canonical curve with normalization 
       $\nu:\  PP^1 \to PP^{g-1}$ then a line bundle L of degree k on C is given by
       $\nu^*(OO_{PP^1}(k))\cong L$ and gluing data 
       $\frac{b_j}{a_j}:OO_{PP^1}\otimes kk(P_j)\to OO_{PP^1}\otimes kk(Q_j)$.
       Given 2g points P_i, Q_i and the multipliers (a_i,b_i) we can compute a basis
       of sections of L as a kernel of the matrix A=(A)_{ij} with
       $A_{ij}=b_iB_j(P_i)-a_iB_j(Q_i)$ where 
       $B_j:PP^1\to kk,\  (p_0:p_1)\to p_0^{k-j}p_1^j$.

     Example
        (k,g,n)=(4,8,1000);
        time (P,Q,multL,f)=pickGoodPoints(k,g,n);
	time f'=lineBundleFromPointsAndMultipliers(multL,P,Q,k);
	ideal f==ideal f'  
  SeeAlso
    canonicalMultipliers
    pickGoodPoints	      
///

doc ///
  Key  
    pickGoodPoints
    (pickGoodPoints, ZZ, ZZ, ZZ)
  Headline 
    computes g pairs of points and gluing data between them 
  Usage
    pickGoodPoints(k,g,n)
  Inputs
       k: ZZ
          the degree of the line bundle
       g: Matrix
          the genus of the curve
       n: ZZ
          defining the characteristic of the ground field (see @TO getFieldAndRing@ for details)
  Outputs
       P: Matrix
          coordinate matrix defining g points P_i
       Q: Matrix
          coordinate matrix defining g points Q_i
       multL: List
          containing the normalized multipliers specifying the line bundle  
       f: Matrix
          containing the two basis sections of the line bundle 	        
  Description
     Text
       Step 1. Searches a morphism $f:PP^1 \to PP^1$ such that det(f|pt_i)
       has at least two linear factors for g distinct points $pt_i \in PP^1.$
       This step is similar to the function @TO listOfFactors@ but without saving 
       quadratic factors.
       
       Step 2. Computes the points P_i,Q_i as the vanishing loci of two of the linear 
       factors of det(f|pt_i).
       
       Step 3. Computes the normalized multipliers, i.e., $b_i=1$ by
       $a_i=\frac{f_0(P_i)}{f_0(Q_i)}$, where $f=(f_0,f_1)^t.$
  SeeAlso
    listOfFactors
    sectionsFromPoints
    idealOfNodalCurveByPoints     
///

doc ///
  Key  
    sparseKoszulMatrix
    (sparseKoszulMatrix, Ideal)
  Headline 
    computes list specifying the size of the critical Koszul map, the nonzero entries and the position of those 
  Usage
    sparseKoszulMatrix(I)
  Inputs
       I: Ideal
          of the canonical curve	  	  
  Outputs
       charkk: ZZ
          the characeristic of the ground field
       rows: ZZ
          the number of rows of the critical Koszul matrix
       cols: ZZ
          the number of columns of the critical Koszul matrix  
       entr: List
          containing the nonzero entries of the critical Koszul 
	  matrix and the position of those        
  Description
     Text
       The function works the same as the function "sparseKoszulMatrixForPrymCurve" in the
       M2 package @HREF("http://www.math.uni-sb.de/ag/schreyer/home/NodalCurves.m2","NodalCurves") @.
       
       Computes the nonzero entries of the Koszul map whose rank determines
       the critical Betti number and the position of these entries. Builds a
       list containing the characteristic of the ground field, the numer of rows, the number
       of columns and a list containing the nonzero entries of the critical Koszul map
       and the position of these entries.

     Example
        (k,g,n)=(4,8,1000);
	I=idealOfNodalCurve(k,g,n);
	(charkk,rows,cols,entr)=sparseKoszulMatrix(I);
	A1=getBackMatrix(charkk,rows,cols,entr);
	A2=criticalKoszulMap(I);
	rank A1==rank A2
	m=ceiling((g-1)/2);
	(Tred,Ired)=artinianReduction(I);
        rank(ker A1)- binomial(g-2,m+1)
        betti res Ired
   
  SeeAlso
    getBackMatrix
    criticalKoszulMap                        
///

doc ///
  Key  
    getBackMatrix
    (getBackMatrix, ZZ,ZZ,ZZ,List)
  Headline 
    reconstructs a matrix from a list of entries and the position of those 
  Usage
    getBackMatrix(charkk,rows, cols, entr)
  Inputs
       charkk: ZZ
          the characeristic of the ground field kk
       rows: ZZ
          the number of rows of a matrix over kk
       cols: ZZ
          the number of columns of a matrix over kk
       entr: List
          containing the nonzero entries of a matrix and the position of those	  	  
  Outputs
       A: Matrix
          the reconstructed matrix        
  Description
     Text
       Reconstructs a matrix from a list of the type as computed by the function
       @TO sparseKoszulMatrix@.

     Example
        (k,g,n)=(4,8,1000);
	I=idealOfNodalCurve(k,g,n);
	(charkk,rows,cols,entr)=sparseKoszulMatrix(I);
	A1=getBackMatrix(charkk,rows,cols,entr);
	A2=criticalKoszulMap(I);
	rank A1==rank A2
	       
  SeeAlso
    sparseKoszulMatrix       
///

doc ///
  Key  
    sectionsFromPoints
    (sectionsFromPoints, Matrix,Matrix)
    (sectionsFromPoints, Sequence)         
  Headline 
    computes matrix defining the canonical embedding from the 2g points 
  Usage
    sectionsFromPoints(P,Q)
    sectionsFromPoints(PQ)
  Inputs
       P: Matrix
          coordinate matrix of g points P_i
       Q: Matrix
          coordinate matrix of g points Q_i
       PQ: Sequence
          containing the matrices P and Q, representing g pairs of points in PP^1	  	  
  Outputs
       s: Matrix
          a matrix of sections defining the canonicl embedding        
  Description
     Text
       Given the g pairs of points P_i,Q_i we can proceed as follows:
       
       Step 1. We compute g quadrics 
       $q_i\ :=det(P_i\ |\ (x_0,x_1)^t)\ *\ det(Q_i\ |\ (x_0,x_1)^t).$
       
       Step 2. We compute a basis of $H^0(C,\omega_C)$ by
       $\{s_i\ :=\prod^g_{j\neq i,j=1}q_i\ |\ i=1,...,g \}$ and multiply
       the matrix $s=(s_1,...,s_g)$ wih a general matrix $M\in GL(g,kk)$
       to obtain more general sections.
       
     Example
         (k,g,n)=(4,8,1000);
         (p,kk,S)=getFieldAndRing(n);
         (P,Q,multL,f)=pickGoodPoints(k,g,n);
         s=sub(sectionsFromPoints(P,Q),S);
         T=kk[t_0..t_(g-1)];
         I=ideal mingens ker map(S,T,s);
         betti res I  
  SeeAlso
    getSections
    idealOfNodalCurveByPoints       
///

doc ///
  Key  
    criticalKoszulMap
    (criticalKoszulMap, ZZ,ZZ,ZZ)    
    (criticalKoszulMap, Ideal)          
  Headline 
    computes the critical Koszul map 
  Usage
    criticalKoszulMap(I)
    criticalKoszulMap(k,g,n)
  Inputs
       k: ZZ
          the degree of the special linebundle
       g: ZZ
          the genus of the constructed curve
       n: ZZ
          defining the characteristic of the ground field (see @ TO getFieldAndRing @ for details)
       I: Ideal
          the ideal of a canonical curve	  	  	  	  	  
  Outputs
       A: Matrix
          the Koszul matrix whose rank determines the critical Betti number        
  Description
     Text
       Constructs a curve with the function @TO idealOfNodalCurve @
       and computes the Artinian reduction of I. Afterwards the function "koszulMap" from the M2 package 
       @HREF("http://www.math.uni-sb.de/ag/schreyer/home/extrasForTheKernel.m2","extrasForTheKernel")@
       is used to compute the critical Koszul map.
       
     Example
        (k,g,n)=(4,8,1000);
	I=idealOfNodalCurve(k,g,n);
	A=criticalKoszulMap(I);
	m=ceiling((g-1)/2);
	rank(ker A)- binomial(g-2,m+1)
	(Tred,Ired)=artinianReduction(I);
	betti res Ired
	        
  SeeAlso
    sparseKoszulMatrix
    criticalBettiNumber
    criticalBettiNumberWithoutArtinanReduction
         
///

doc ///
  Key  
    criticalBettiNumber
    (criticalBettiNumber, ZZ,ZZ,ZZ)   
    (criticalBettiNumber, Ideal)     
  Headline 
    computes the critical Betti number 
  Usage
    criticalBettiNumber(k,g,n)  
    criticalBettiNumber(I)
  Inputs
       k: ZZ
          the degree of the special pencil
       g: ZZ
          the genus of the constructed curve
       n: ZZ
          defining the characteristic of the ground field (see @ TO getFieldAndRing @ for details)
       I: Ideal
          ideal of a canonical curve	  	  	  	  
  Outputs
       b: ZZ
          the critical Betti number 	  	  	  	        
  Description
     Text
       Computes the Artinian reduction of the ideal of a canonical curve and the
       critical Koszul map. Afterwars we compute the critical Betti number via Koszul
       cohomology. 
       The M2 package @HREF("http://www.math.uni-sb.de/ag/schreyer/home/extrasForTheKernel.m2","extrasForTheKernel")@
       provides a function that computes the artinian reduction.
       
     Example
        (k,g,n)=(4,8,1000);
	I=idealOfNodalCurve(k,g,n);
	time criticalBettiNumber(I)
	time criticalBettiNumber(k,g,n)
	time betti res I    
  SeeAlso
    criticalBettiNumberWithoutArtinanReduction
    criticalKoszulMap	   
///

doc ///
  Key  
    criticalBettiNumberWithoutArtinanReduction
    (criticalBettiNumberWithoutArtinanReduction, ZZ,ZZ,ZZ)   
    (criticalBettiNumberWithoutArtinanReduction, Ideal)     
  Headline 
    computes the critical Betti number 
  Usage
    criticalBettiNumberWithoutArtinanReduction(k,g,n)  
    criticalBettiNumberWithoutArtinanReduction(I)
  Inputs
       k: ZZ
          the degree of the special pencil
       g: ZZ
          the genus of the constructed curve
       n: ZZ
          defining the characteristic of the ground field (see @ TO getFieldAndRing @ for details)
       I: Ideal
          ideal of a canonical curve	  	  	  	  
  Outputs
       b: ZZ
          the critical Betti number       
  Description
     Text
       Computes the critical Betti number of a canonical curve 
       via Koszul cohomology. 
       
     Example
        (k,g,n)=(4,8,1000);
	I=idealOfNodalCurve(k,g,n);
	time criticalBettiNumberWithoutArtinanReduction(I)
	time criticalBettiNumberWithoutArtinanReduction(k,g,n)
	betti res I
	       
  SeeAlso
    criticalBettiNumber
    criticalKoszulMap      
///
