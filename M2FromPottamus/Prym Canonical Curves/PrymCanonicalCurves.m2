newPackage(
	"PrymCanonicalCurves",
    	Version => "0.2", 
    	Date => "March 8, 2012",
    	Authors => {{Name => "Frank-Olaf Schreyer", 
		  Email => "schreyer@math.uni-sb.de", 
		  HomePage => "http://www.math.uni-sb.de/ag/schreyer/"}
                   },
    	Headline => "Construction of random Prym canonical curves",
    	DebuggingMode => true
        )


export{getSepticOfGenus8With2Torsion,
     getCanonicalCurveOfGenus8With2Torsion,
     randomPrymCanonicalCurveOfGenus7,
     randomOneNodalPrymCanonicalCurveOfGenus8,
     check2Torsion,
     addANodeAndExtend2Torsion,
     simplifyDivisor,
     prymCanonicalEmbedding,
     getAPrymCanonicalCurve,
     extraSyzygyInGenus8}

needsPackage("extrasForTheKernel")





  
getSepticOfGenus8With2Torsion=method()
getSepticOfGenus8With2Torsion(PolynomialRing):= (S) -> (
     if numgens S=!=3 then error "expect a polynomial ring in 3 variables";
     kk:=coefficientRing S;
     r:=symbol r;
     R:=kk[r_0,r_1]; -- coordinate ring of P^1
     trials:=1; -- we will use a probalistic method to get the 8 tangencies, 
     -- which in a single trial in 62.5 % of the cases. Thus a few repetition
     -- will do.
     while (
	  m:=random(R^2,R^{3:-1}); 
	  -- 3 pairs of linear forms, which defining six points in P^1
	  phi0:=matrix{apply(3,i->product(3,j->if i==j then 1_R else m_(0,j)*m_(1,j)))};
	  -- parametrization of the 3 nodal quartic, which identifies the two points for each of the 3 pairs
	  phi:=map(R,S,phi0);
	  g0:=ker phi; -- ideal of the three nodal quartic Q
	  singg0:=saturate ideal jacobian g0; -- and its singular loci
	  pts:=random(R^2,R^6); -- 6 further points on P^1
	  L1:=apply(6,i->ideal(vars S*substitute(syz substitute(phi0, transpose pts_{i}),S)));
	  -- the List of the ideal of the images under phi
	  L2:=apply(L1,J->saturate(J^2+g0)); -- list of the ideals 
          --  of the tangent vectors to  in these points
	  Itang:=intersect L2; -- the tangency condition for 6 points
	  q:=ideal random(S^1,S^{2:-2}); -- 4 further points i P^2
	  betti( G:=(gens saturate intersect(q^2,singg0^2,Itang))_{0,1,2});
	  -- linear system of septics double in the singular points of Q 
	  -- and the four further points, which moreover are tangent to Q 
	  -- at the the 6 choosen points, G is a net because
	  binomial(7+2,2)-7*3-2*6==3;
	  Itang0:=(gens saturate substitute(Itang,phi0))_(0,0); 
	  -- pull back of the tangency condition to P^1
	  singg02:=(gens (saturate substitute(singg0,phi0))^2)_(0,0); 
	  -- pull back of the singular points of Q double
          G1:=matrix{apply(3,i->lift(substitute (G_(0,i),phi0)/Itang0/singg02,R))};
	  --pull back of the linear system G to P^1 with base loci removed.
	  --Since 4*7==3*4+2*6+4 the system G1 is a net of binary quartics.
	  --We want to find a square of a quadric in this net.
	  --For this we compute the ideal squares in k[s,t]_4.
	  a:=symbol a; b:= symbol b; 
          A:=kk[a_0..a_2],B:=kk[b_0..b_4];
	  --coordinates for k[s,t]_2 and k[s,t]_4.
	  RA:=R**A,RB:=R**B;
	  rr:=substitute(vars A,RA)*substitute(transpose gens (ideal vars R)^2,RA);
	  mA:=substitute(contract(substitute(gens(ideal vars R)^4,RA),rr^2),A);
	  VS:=ker(phi=map(A,B,mA)); -- Veronese surface of squares in P(H^0(P^1,O(4)))=P^4
          -- betti res VS
	  -- Now we use A also for coordinates for the net G1
	  GA:=substitute(G1,RA)*transpose substitute( vars A,RA); 
	  -- generic element of the net G
	  mB:=substitute(contract(substitute(gens(ideal vars R)^4,RA),GA),A);
	  -- parametrization of the net in P^4
	  fourPts:=saturate substitute(VS,mB);  --ideal of the intersection of VS 
          -- with the P^2 in P^4 -- ie. the ideal of four points in P^2
	  cfourPts:=decompose fourPts; 
          -- we look for a kk-rational point among these four point. The probabilty 
	  -- that we have such a point is the proportion of permutations with fixed points in 
	  -- the symmetric group of 4 elements, hence 62.5 %
	  Lpts:=select(cfourPts,pt->degree pt==1);
	  #Lpts==0) do trials=trials+1;
     C:=ideal((G*substitute(syz transpose jacobian Lpts_0,S))_(0,0));
     -- C the desired curve with tangent to Q at eight points
     D0:= radical saturate(C+g0,singg0);
     assert(degree D0==8);
     D1:=saturate(ideal(g1:=gens singg0*random(S^{3:-2},S^{-2})) + C,singg0);
     assert(degree D1==8);
     --Pts:=apply(n,i->randomKRationalPoint(C));
     (C,{D0,D1}))



getCanonicalCurveOfGenus8With2Torsion=method()
getCanonicalCurveOfGenus8With2Torsion(PolynomialRing,ZZ):=(R,n)->(
     --R an PolynomialRing in 8 variables
     --n the number of additionalPoints
     if numgens R =!= 8 then error "expected a polynomial ring with 8 variables";
     kk:= coefficientRing R;
     if char kk ==0 then error "expected a finite ground field";
     x:= symbol x;
     S:=kk[x_0..x_2];
     (I,Da):=getSepticOfGenus8With2Torsion(S);
     assert( degree I==7 );
     singI:= saturate( ideal jacobian I+I);
     assert( degree singI==7);
     assert( dim (minors(2,jacobian singI)+singI)==0);
     phi:=gens truncate(4,singI);
     assert( rank source phi==8);
     SI:=S/I;
     J:=ideal mingens ker map(SI,R,sub(phi,SI)); 
     D:=apply(Da,d->(Sd:=S/d;ideal mingens ker map(Sd,R,sub(phi,Sd)))); 
     Ptsa:=apply(n,i->randomKRationalPoint(I));
     Pts:=apply(Ptsa,pt->(Sp:=S/pt;ideal mingens ker map(Sp,R,sub(phi,Sp))));
     (J,D,Pts)) 

randomPrymCanonicalCurveOfGenus7=method()
randomPrymCanonicalCurveOfGenus7(PolynomialRing):= R -> (
     if numgens R =!= 6 then error "expected a polynomial ring with 6 variables";
     kk:= coefficientRing R;
     if char kk == 0 then error "expected a finite ground field";
     z:= symbol z;
     S:=kk[z_0,z_1];-- homogeneous coordinate ring of P^1
     linsys:=basis(5,S);
     phi:=map(S,R,linsys);
     IC5:=ker phi; --rational normal curve of degree 5
     pts:=random(S^1,S^14);
     while(#unique flatten entries pts =!=14) do pts=random(S^1,S^14);
     Sp:=S;
     pts1:=apply(14,i->ideal(pts_(0,i)*z_0-z_1));
     pts2:=apply(pts1,pt->(Sp=S/pt;ker map(Sp,R,sub(linsys,Sp))));
     Lines:=apply(7,i->ideal (mingens intersect(pts2_i,pts2_(i+7)))_{0..3});
     J:=intersect(intersect(Lines),IC5);-- singular Prym curve C0 of genus 7,
     -- the union of a rational normal curve of degree 5 defined by IR with 7 secant line
     nikulin:=ideal (gens J)_{0..2}; -- Niculin surface
     --get general C in |C0| on the Nikulin surface
     H3:=ideal( gens J*random(source gens J, R^{ -3}))+nikulin;--cubic through C0
     IC1:=H3:J; -- the linked curve
     H3a:=ideal( gens IC1*random(source gens IC1, R^{ -3}))+nikulin;
     IC:=H3a:IC1; -- double link
     IC)

TEST ///
     p=nextPrime(10^4)
     R=ZZ/p[x_0..x_5] -- homogeneous coordinate ring of P^5
     I=randomPrymCanonicalCurveOfGenus7(R)
     assert( (dim I,degree I,genus I)==(2,12,7) )
/// 

randomOneNodalPrymCanonicalCurveOfGenus8=method()

randomOneNodalPrymCanonicalCurveOfGenus8(PolynomialRing):= R -> (
     if numgens R =!= 7 then error "expected a polynomial ring with 6 variables";
     kk:= coefficientRing R;
     if char kk ==0 then error "expected a finite ground field";
     z:= symbol z;
     S:=kk[z_0..z_5]; -- homogenous coordinate ring of P^5
     IC:=randomPrymCanonicalCurveOfGenus7(S);
     fIC:=res IC;
     K1:=fIC.dd_4*random(S^{7:-6},S^{6:-6});
     KC:=annihilator coker transpose K1; -- canonical divisor of C
     SR:=S**R;
     graph:=sub(vars R,SR)*transpose sub(fIC.dd_4,SR);
     presL:=map(R^6,R^{24:-1},sub(diff(transpose sub(vars S,SR),graph),R));
     Ican:=annihilator coker presL; 
     D1:=saturate annihilator coker (random(R^5,R^6)*presL);
     D2:= ideal mingens (Ican+ideal random(1,R));
     -- D1-D2 is a 2 Torsion divisor
     -- pick a few more points
     pts:=apply(10,i->randomKRationalPoint(Ican));
     (J,E,Pts1):=addANodeAndExtend2Torsion(Ican,{D1,D2},pts);
     E0:=E_0;E1:=E_1;
     T:=ring J; -- coordinate ring of P^7 of the nodal canonical curve C=V(J)
     H1:=gens E1*random(source gens E1,T^{-2});
     E1linked:=(ideal H1+J):E1;
     prymSys:=intersect(E1linked,E0);
     prymSys1 := (gens prymSys)_{15..21};
     TJ:=T/J;
     phi:=map(TJ,R,sub(prymSys1,TJ));
     I:=ideal mingens ker phi; -- the Prym canonical nodal curve     
     I)
TEST ///
     p=nextPrime(10^4)
     R=ZZ/p[x_0..x_6] -- homogeneous coordinate ring of P^6
     I=randomOneNodalPrymCanonicalCurveOfGenus8(R)
     assert( (dim I, degree I, genus I)==(2,14,8))
///     
     
    

check2Torsion=method()
check2Torsion(Ideal,List):=(J,D)->(
     twoD0:=saturate(D_0^2+J);
     f0:=(mingens ideal (gens twoD0%J))_(0,0);
     E0:=(J+ideal f0:D_0):D_0;
     betti(twoD1:=saturate(D_1^2+J));
     f1:=mingens ideal(gens intersect(E0,twoD1)%J);
     T:=tally degrees source f1;
     assert(T_(degree f0)==1);
     {f0,f1_(0,0)})

addANodeAndExtend2Torsion=method()
addANodeAndExtend2Torsion(Ideal,List,List):=(I,D,Pts)->(
     S:=ring I;
     kk:=coefficientRing S;
     tt:=symbol tt;
     T:=kk[tt];
     f:=check2Torsion(I,D);
     Pts1:=Pts;Pts2:={};Mu:=0;mu:=0;comp:=0;pts:=0;
     while (
	  pts=apply(2,j->substitute((transpose syz transpose jacobian Pts1_j),kk)); 
	  Mu=matrix apply(2,i->apply(pts,pt->substitute(f_i,pt)));
	  mu=(Mu_(0,0)/Mu_(1,0))/(Mu_(0,1)/Mu_(1,1));
     	  comp=decompose ideal (tt^2-mu);
     	  #comp<2) do (Pts2=append(Pts2,Pts1_0);Pts1=drop(Pts1,1));
     lambda:=substitute(tt%(decompose ideal (tt^2-mu))_0,kk);
     g:={random(1,ring I),random(1,ring I)};
     gps:=matrix apply(g,gi->apply(pts,pt->substitute(gi,pt)));
     G:=matrix{{1,1},{1,1/lambda}}*inverse gps*transpose matrix{g};
     D0:=saturate(D_0*ideal G_(0,0)+I);
     D1:=saturate(D_1*ideal G_(1,0)+I);
     pq:=intersect(Pts1_0,Pts1_1);
     H:=(gens pq)_(0,0);
     E:=(I+ideal H):pq;
     phi:=mingens ideal((gens truncate(2,E))%I);
     n:=rank source phi-1;
     x:= symbol x;
     R:=kk[x_0..x_n];
     SI:=S/I;
     betti(J:=ideal mingens ker map(SI,R,sub(phi,SI)));
     S0:=ring D0/D0;
     D0=ideal mingens ker map(S0,R,sub(phi,S0));
     S1:=ring D1/D1;
     D1=ideal mingens ker map(S1,R,sub(phi,S1));
     Pts1=join(drop(Pts1,2),Pts2);     
     Pts1=apply(Pts1,pt->(Sp:=S/pt;ideal mingens ker map(Sp,R,sub(phi,Sp))));
     (J,{D0,D1},Pts1))



simplifyDivisor=method()
simplifyDivisor(Ideal,List,List):=(I,D,Pts)->(
     R:=ring I;
     H0:=(mingens ideal(gens D_0 % I))_(0,0);    
     E0:=mingens ideal (gens(I+ideal H0:D_0)%I);
     H1:=(mingens ideal(gens D_1 % I))_(0,0);    
     E1:=mingens ideal (gens(I+ideal H1:D_1)%I);
     m:=min(rank source E0,rank source E1)-1;
     assert((tally degrees source E0)_(degree H0)>=m+1);
     assert((tally degrees source E1)_(degree H0)>=m+1);
     B:=intersect apply(m,i->Pts_i);
     B0:=(mingens ideal((gens intersect(ideal E0+I,B))% I))_(0,0);
     betti(D0:=((ideal B0 +I):B):(ideal E0+I));
     
     B1:=(mingens ideal((gens intersect(ideal E1+I,B))% I))_(0,0);
     betti(D1:=((ideal B1 +I):B):(ideal E1+I));
     ({D0,D1},drop(Pts,m)))


prymCanonicalEmbedding=method()
prymCanonicalEmbedding(Ideal,List):=(I,D)->(
     H:=(mingens ideal((gens D_0)%I))_(0,0);
     E:=(ideal H + I):D_0;
     phi:=mingens ideal((gens intersect(E,D_1))%I) ;    
     n:=rank source phi-1;
     kk:=coefficientRing ring I;
     x:=symbol x;
     R:=kk[x_0..x_n];
     RI:=ring I/I;
     J:=ideal mingens ker map(RI,R,sub(phi,RI));     
     J)


    	  
getAPrymCanonicalCurve=method()
getAPrymCanonicalCurve(ZZ,ZZ):=(g,p)->(
     if g<8 then error "only implemented for curves of genus >7";
     kk:=ZZ/nextPrime(p);
     x:= symbol x;
     S:=kk[x_0..x_7];
     t:=5;--number of trials to find a square
     n:=sum(8..g-1,h->h+2*h-2-(h+2))+(g-8)*(1+t); -- the number of points needed
     time (I,D,Pts):=getCanonicalCurveOfGenus8With2Torsion(S,n);     
     h:=8;     
     while h<g do (time (I,D,Pts)=addANodeAndExtend2Torsion(I,D,Pts);h=h+1);
     prymCanonicalEmbedding(I,D))

extraSyzygyInGenus8=method()

extraSyzygyInGenus8(Ideal) := I-> (
     fI:=res(I,LengthLimit=>2);
     pt1:=fI.dd_2_{0};
     -- the quadrics involved in the linear syzygy
     J:=ideal(fI.dd_1*syz transpose syz(transpose pt1,DegreeLimit=>-2));
     pt:=ideal mingens ideal pt1;-- the ideal of a point
     halfCan:=J:pt; -- a half canonical curve of genus 22 consisting of two componets
     E:=halfCan:I; -- an elliptic normal curve component
     (pt,E))


beginDocumentation()

doc ///
  Key
    PrymCanonicalCurves
  Headline
    construction of Prym canonical curves     
  Description
    Text
      {\bf What's new:}

      {\it Version 0.3}      
     

      {\bf Overview:}
         We randomly construct smooth Prym canonical curves of genus 7 over a finite prime field based on the unirationality proof of
	 @ HREF("http://arxiv.org/abs", "Farkas, Verra [2012]") @.
	 We then add a node to these curve to obtain a random 1-nodal Prym canonical curve of genus 8.
	 We also have a construction of smooth Prym canonical curve of genis 8, which are not general in their moduli space, 
	 because they have a plane model of degree 7. For more see "getCanonicalCurveOfGenus8With2Torsion".
         Starting from these curves we construct Prym canonical curves of higher genus by adding nodes.
         The main goal is to verify the Prym Green conjecture @ HREF("http://arxiv.org/abs/0804.4616", "Farkas, Ludwig [2008]") @  for small values of g.
	 
	 The conjecture says that a general Prym canonical curve of even genus has a pure resolution.
	 In case of genus g=8 the verification fails: We always find one extra syzygy. In the range g=10..14 
	 the verification  works, g=16 gives again one extra syzygy. Experiments for the last cases are however expensive in cpu time and memory.
	 
	 Finally we study the extra syzygy in genus 8. For more on this, see "extraSyzygyInGenus8". 
     
      
      

      {\bf Setup:}

      This package requires Macaulay2 version 1.4 or newer.

      Install this @TO Package@ by doing

      @TO installPackage@("NodalCurves")

      {\bf Examples:}
///


doc ///
  Key
    getSepticOfGenus8With2Torsion
    (getSepticOfGenus8With2Torsion,PolynomialRing)
  Headline
    Construct a plane septic curve C of geometric genus 8 together with a 2-torsion divisor
  Usage
    (I,D)=getSepticOfGenus8With2Torsion(S)    
  Inputs
    S: PolynomialRing
       a polynomial ring in 3 variables over a finite ground field kk
  Outputs
    I: Ideal
       of a plane septic curve C of geometric genus 8 with 7 double points.
    D: List
       a pair of divisors \{D_0,D_1\}\ specified by ideals of a collection of points
       on C, such that D_0-D_1 is 2-torsion in Pic C.
  Description
     Text 
       We construct a curve C of genus 8 with a g^2_7 together with a 2-torsion divisor.
       The model C' of C in P^2 has 7 double points. The divisor D_0 will consist 
       of eight points in which C' and a rational quartic Q  are tangent.
       We choose Q and C' such that they have three double points in common.
       Since 7*4-3*2^2==2*8 there are no more intersection points. The divisor D_1
       will be given by the 8=7*2-3*2 additional intersection points of C' with a conic defined by g_1 
       through the 3 singular points.
       Note that D_0-D_1 is 2-torsion in Pic C.
            
     Example
       p=10007;kk=ZZ/p;
       S=kk[x_0..x_2]
       time (I,D)=getSepticOfGenus8With2Torsion(S);
       dim I, degree I 
       geometricGenus=genus I - degree ideal jacobian I 
       
     Text
       Key idea of the construction is the following: Choose a parametrization of the quartic Q first,
       together with 6 of the desired 8 points of tangency. The linear system of septics double at 
       at the 7=3+4 points and tangent to Q in the 6 given point is a net. We find the desired
       C in the net by the condition that the remaining 4 points on P^1 are defined by a square.
       More precisely, we consider the intersection of the net with the Veronese surface of squares 
       inside P(H^0(P^1,O(4)))^*. This are 4 points and for random choice we expect a 
       kk-rational intersection points in 62.5% of the cases. Thus a probabilistic approach works.      
/// 

doc ///
  Key
    getCanonicalCurveOfGenus8With2Torsion
    (getCanonicalCurveOfGenus8With2Torsion,PolynomialRing,ZZ)
  Headline
    Construct a canonical curve C of genus 8 together with a 2-torsion divisor and n extra points
  Usage
    (I,D,Pts)=getCanonicalCurveOfGenus8With2Torsion(S,n)    
  Inputs
    S: PolynomialRing
       a polynomial ring in 8 variables over a finite ground field kk
    n: ZZ
       the desired number of extra points
  Outputs
    I: Ideal
       of a canonical curve C of genus 8.
    D: List
       a pair of effective divisors \{D_0,D_1\} specified by ideals of a collection of points
       on C, such that D_0-D_1 is 2-torsion in Pic C.
    Pts: List
       of ideals of n further kk-rational points on C
  Description
     Text 
       We construct a curve C of genus 8 with a g^2_7 together with a 2-torsion divisor,
       via its plane model and transfer the data into canonical space.
    
     Example
       kk=ZZ/10007;R=kk[x_0..x_7];
       time (J,D,Pts)=getCanonicalCurveOfGenus8With2Torsion(R,2);
       time betti res J
       apply(D,d->(dim d,degree d))       
       tally apply(Pts,pt->betti pt)     
///

 


doc ///
  Key
    check2Torsion
    (check2Torsion,Ideal,List)
  Headline 
    Check that D_0-D_1 represents is a two torsion divisor on the curve defined by J 
  Usage
    check2Torsion(I,D)
  Inputs
    I: Ideal 
       of a (projectively normal) curve C
    D: List
       a pair \{D_0,D_1\} of two effective divisors represented by their ideals
  Outputs
    f: List
       a pair \{f_0,f_1\}  of forms of equal degree such that
       (f_0/f_1)= 2(D_0-D_1) in Pic C.
  Description
     Text
       We compute a rational function f_0/f_1 represented by homogeneous forms which verify
       the two torsion claim and make this assertion.	  
     Example
       kk=ZZ/10007;R=kk[x_0..x_7];
       time (J,D,Pts)=getCanonicalCurveOfGenus8With2Torsion(R,4);
       f=check2Torsion(J,D)
///

doc ///
  Key
    addANodeAndExtend2Torsion
    (addANodeAndExtend2Torsion,Ideal,List,List)
  Headline
    add a node to a canonical curve and extend a 2-Torsion divisor to the new curve
  Usage
    (J,E,Pts1)=addANodeAndExtend2Torsion(I,D,Pts)
  Inputs
    I: Ideal 
       of a curve C in its canonical embedding over a finite field kk
    D: List
       a pair \{D_0,D_1\} of two effective divisors represented by their ideal
    Pts: List
       a list of ideals of kk-rational points on C
  Outputs
    J: Ideal
       of canonical curve C' obtained by identifying two points from the list to anode
    E: List
       a pair of divisors \{E_0,E_1\} such that E_0-E_1 is two torsion on C'
    Pts1: List
    	 of ideals of the remaining points on C'
  Description
     Text
       Given a canonical possibly nodal curve C and a two Torsion divisor
       D_0-D_1, we compute a curve C' obtained by identifying two points p, q on C
       to a node, and a 2-Torsion line bundle whose pullback under C-> C' 
       is the given 2 Torsion line bundle O_C(D_0-D_1). Note that C' 
       together E_0-E_1 is defined over the given ground field if and only if
       the values of the rational function f with (f)=2D_0-2D_1
       at the two points p, q differ by a square, i.e. f(p)/f(q) \in kk^2.
       We use a probabilistic approach to over come this difficulty, 
       by trying several pairs of points if necessary.
     Example
       kk=ZZ/10007;R=kk[x_0..x_7];
       time (J,D,Pts)=getCanonicalCurveOfGenus8With2Torsion(R,20);
       betti J, dim J, codim J, degree J, genus J, apply(D,d->degree d)
       time (I,D,Pts)=addANodeAndExtend2Torsion(J,D,Pts); 
       betti I, dim I, codim I, degree I, genus I, apply(D,e->degree e)
       (E,Pts1)=simplifyDivisor(I,D,Pts);
       apply(E,e->degree e)
       #Pts,#Pts1
       betti(J=prymCanonicalEmbedding(I,E)), dim J,codim J,degree J,genus J
     Text
       The key idea of the algoritm to compute a rational function g
       such that f(p)/f(q)*(g(p)/g(q))^2 = 1. The function g can be obtained 
       from any pencil of homogeneous forms via a suitable fractional 
       transformation. We compute suitable linear forms g_0,g_1 such that
       g=g_0/g_1 has the desired property and replace D_i by 
       E_i+g_i.C for i=0,1. The curve C' is simply the image of
       C under |K_C+p+q|. The divisor representative E_0,E_1 of the divisor 
       class E_0-E_1 can be simplified by imposing common base points
       in both |E_i|. This can be carried out with the function "simplifyDivisor",
       but it is not in the current routine "addANodeAndExtend2Torsion".
///       

doc ///
  Key
    simplifyDivisor
    (simplifyDivisor,Ideal,List,List)
  Headline
    Simplify the representation of a divisor on a curve.
  Usage
    (E,Pts1)=simplifyDivisor(J,D,Pts)
  Inputs
    I: Ideal 
       of a projectively normal curve C
    D: List
       a pair \{D_0,D_1\} \ of two effective divisors on C
       represented by their ideal
    Pts: List
       of ideals of kk-rational points on C 
  Outputs
    E: List
       a pair \{E_0,E_1\} \ of effective divisors given by their ideals, which
       represent the same class as D_0-D_1.
    Pts1: List 
       of ideals of the remaining kk-rational points on C     
  Description
     Text
       We impose common base points from the list Pts on both linear systems |D_i| 
       to obtain a simpler representation E=\{E_0,E_1\} \ of
       the divisor class $ D_0-D_1 \cong E_0-E1$. 
///

doc ///
  Key
    prymCanonicalEmbedding
    (prymCanonicalEmbedding,Ideal,List)
  Headline
    Compute the Prym canonical image
  Usage
    prymCanonicalEmbedding(I,D)
  Inputs
    I: Ideal 
       of a projectively normal curve C
    D: List
       a pair \{D_0,D_1\} of two effective divisors on C
       represented by their ideals such that D_0-D_1 is two torsion in Pic C
  Outputs
     : Ideal
       the defining ideal of the image of C under K_C+D_0-D_1  
  Description
     Text
       We compute the ideal of the image of C under the Prym canonical map.
///

doc ///
  Key
    getAPrymCanonicalCurve
    (getAPrymCanonicalCurve,ZZ,ZZ)
  Headline
    get a Prym canonical curve
  Usage
    prymCanonicalEmbedding(g,p)
  Inputs
    g: ZZ 
       the genus of the desired curve
    p: ZZ
       approximately the characteristic of the ground field
  Outputs
     : Ideal
       defining a Prym canonical curve of genus g \ge 8
  Description
     Text
       We compute the ideal of a Prym canonical of genus g over a finite ground field
       by starting with a smooth anonical curve of genus 8 with two torsion. 
       We add nodes and extend the two torsion untill we reach the desired genus.
       The curve of genus 8 has a plane modell of degree 7. Hence is somewhat special.
       The resulting curve get nodes by identifying random two points. The time reaching
       the curve of each intermediate genus will be printed reported.
     Example
       betti(J=getAPrymCanonicalCurve(9,10^4))
       dim J, codim J, degree J, genus J
///

doc ///
  Key
    randomPrymCanonicalCurveOfGenus7
    (randomPrymCanonicalCurveOfGenus7,PolynomialRing)
  Headline
    pick a random Prym canonical curve of genus 7
  Usage
    I=randomPrymCanonicalCurveOfGenus7(R)    
  Inputs
    R: PolynomialRing
       in six variables, the homogeneous coordinate ring of P^5 over a finite ground field
  Outputs
    I: Ideal
       of a Prym canonical curve of genus 7
  Description
     Text
       Acoording to @ HREF("http://arxiv.org/abs", "Farkas, Verra [2012]") @ the moduli space R_7 of Prym canonical curves of genus 7
       is unirational. The proof is bassed on the fact that a general Prym canonical embedded curve C of genus 7 lies on a unique Nikulin surface X,
       the intersection of the three quadrics in the homogeneous ideal of C. If $L_1, \ldots, L_8$ denote the 8 lines on the Nikulin surface
       then the linear system $|C-(L_1+\ldots+L_7)|$ is zero dimensional and consists of a rational normal curve C5 which has $ L_1, \ldots , L_7$ 
       as secants lines. 
       The unirational construction reverses this observation. The union $C5 \cap L_1 \cap \ldots \cap L_7 \subset \mathbb P^5$ of a rational normal 
       curve of degree 5 with seven general secant lines is contained in a unique Nikulin surface X, and a general $C \in |R5+L_1+\ldots+L_7|$ on X
       gives the desired general $C \in R_7$.
     Example
        p=10007,kk=ZZ/p,R=kk[x_0..x_5]
        time I=randomPrymCanonicalCurveOfGenus7(R);
        (dim I,degree I, genus I)
	betti res I
/// 


doc ///
  Key
    randomOneNodalPrymCanonicalCurveOfGenus8
    (randomOneNodalPrymCanonicalCurveOfGenus8,PolynomialRing)
  Headline
    pick a random Prym canonical curve of arithmetic genus 8 with one node
  Usage
    I= randomOneNodalPrymCanonicalCurvesOfGenus8(R)    
  Inputs
    R: PolynomialRing
       in seven variables, the homogeneous coordinate ring of P^6 over a finite ground field
  Outputs
    I: Ideal
       of a Prym canonical curve of of arithmetic genus 8 with one node
  Description
     Text
       The functions starts with a random Prym canonical curve C of genus 7, say embedded by $K_C \otimes L$. Then it picks randomly two points p,q on 
       C such that the curve $C_{p=q}$ of genus 8 
       obtained identifying p and q carries a two torsion line bundle $L_pq$ such that L_{pq} pulls back to L under the normalization map
       $C \to C_{p=q}$. The ideal of the curve $C_{p=q}$ embedded by $|K_{C_{p=q} \otimes L_{pq}|$ is returned.
     Example
        p=10007,kk=ZZ/p,R=kk[x_0..x_6]
        time I=randomOneNodalPrymCanonicalCurveOfGenus8(R);
        (dim I,degree I, genus I)
	betti res I
///

doc ///
  Key
    extraSyzygyInGenus8
    (extraSyzygyInGenus8,Ideal)
  Headline
    study the extra syzygy of a random Prym canonical curve of genus 8
  Usage
    (pt,E) = extraSyzygyInGenus8(I)   
  Inputs
    I: Ideal
       of a curve C of genus 8 and degree 14 in P^6 with an extra syzygy
  Outputs
    pt: Ideal
        of a point
    E:  Ideal 
        of an elliptic normal curve of degree 7 
  Description
     Text
       The function decomposes the syzygy scheme of the extra syzygy into its component.
       The six quadrics involved in the syzygy vanish in the union of C with an elliptic normal curve E and a point pt. 
     Example
       p=10007, R=ZZ/p[x_0..x_6];
       time I = randomOneNodalPrymCanonicalCurveOfGenus8 R;
       betti res I
       (dim I ,degree I, genus I)==(2,14,8)
       (pt,E)=extraSyzygyInGenus8 I ;
       (dim E, degree E, genus E)==(2,7,1)   
       betti res E
       (dim pt, degree pt)==(1,1)
       halfCan=intersect(E,I);
       betti res halfCan     
       (dim halfCan, degree halfCan, genus halfCan)==(2,21,22)
       betti res intersect(E,I,pt)
       (dim(I+E),degree(I+E))==(1,14)
///

end;

	

----------------------------------
--- End of PrymCanonicalCurves.m2
----------------------------------




restart
loadPackage("extrasForTheKernel",Reload=>true)
loadPackage("PrymCanonicalCurves",Reload=>true)
uninstallPackage("PrymCanonicalCurves")
installPackage("PrymCanonicalCurves",RerunExamples=>true,RemakeAllDocumentation=>true);


