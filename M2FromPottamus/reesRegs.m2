--needsPackage "ReesAlgebra"
w := global w;
{*
reesIdeal = method(Options => {Variable => w})

reesIdeal (Module, RingElement) := Ideal => o -> (M,a) -> (
     R:= ring M;
     if R =!= ring a 
     then error("Expected Module and Element over the same ring");   
     P := presentation M;
     sourceDegs := apply(degrees target P, i -> prepend(1,i));
     RSourceTemp:=(coefficientRing R)(monoid[w_1..w_(rank target P)]**monoid R);
     RSource:=newRing(RSourceTemp, 
	  Degrees=>join(sourceDegs,drop ( (monoid RSourceTemp).Options.Degrees, rank target P)));
     NewVars:=matrix{apply(rank target P, i->RSource_i)};
     I := ideal (NewVars*(substitute(P, RSource)));
     a = substitute(a, RSource);
     saturate(I,a)
     )

reesIdeal(Ideal, RingElement) := Ideal => o -> (I,a) -> (
     reesIdeal(module I, a)
     )

reesIdeal(Ideal) := Ideal => o -> (I) -> reesIdeal(I, I_0)
*}

YRRvYRF_BROKEN= i->(
     --compare the y-rees regularity with that of the fiber ring:
     L := reesIdeal(i,i_0);
     RRR := (coefficientRing ring i)[W_1..W_(numgens i),Z_1..Z_(numgens ring i), 
	  Degrees=>toList(((numgens i):{0,1})|((numgens ring i):{1,0}))];
     f=map(RRR,ring L,vars RRR);
     newI:= f L;
     oldvars:=(gens RRR)_{numgens RRR-numgens ring i..numgens RRR-1};
     RRR1 := (coefficientRing RRR)[W_1..W_(numgens i)];
     g:=map(RRR1,RRR, (vars RRR1)|matrix{{numgens ring i:0_RRR1}});
     if regularity betti(newI,Weights=>{0,1})!= (regularity g newI)-1 then (
     print i;
     print newI;
     print (regularity betti(newI,Weights=>{0,1}));
     print (g newI);
     print ((regularity g newI)-1);
     ))

YRRvYRF= i->(
     --compare the y-rees regularity with that of the fiber ring:
     L := reesIdeal(i,i_0);
     RRR := (coefficientRing ring i)[W_1..W_(numgens i),Z_1..Z_(numgens ring i), 
	  Degrees=>toList(((numgens i):{0,1})|((numgens ring i):{1,0}))];
     f:=map(RRR,ring L,vars RRR);
     newI:= f L;
     oldvars:=(gens RRR)_{numgens RRR-numgens ring i..numgens RRR-1};
     RRR1 := (coefficientRing RRR)[W_1..W_(numgens i)];
     g:=map(RRR1,RRR, (vars RRR1)|matrix{{numgens ring i:0_RRR1}});
     yrr:=YRR i;
     if yrr!= (regularity g newI)-1 then (
     print i;
     print newI;
     print yrr;
     print (g newI);
     print ((regularity g newI)-1);
     ))
 
///
--compare the regularity of the fiber ring with that of the Rees ring.
--Always equal in the case of a primary ideal gen by forms of same degree?
--yes for lots of monomial and nearly monomial examples with few
--generators, as below.
restart
load "reesRegs.m2"
S=kk[x,y]
i=ideal"x5,y5, x3y2"

YRRvYRF i

S=kk[x,y,z,u]
use S
j=ideal(x^3,y^3,z^3,u^3,x*y*z+x*y*u)
YRR j
time YRRvYRF j


S=kk[x,y,z,u]
d=4
i0=ideal(x^d, y^d, z^d,u^d)
time for p from 1 to d-1 do(
     for q from 1 to d-p do(
	  for m from 0 to d-p-q do(
	  r=d-p-q-m;
	  print(p,q,m,r);
     	  for p1 from 1 to d-1 do(
	         for q1 from 1 to d-p1 do(
		      for m1 from 1 to d-p1-q1 do(
	  r=d-p-q-m;
	  r1=d-p1-q1-m1;
	  YRRvYRF (i0 +ideal(x^p1*y^q1*z^r1*u^m1+x^p*y^q*z^r*u^m))))))))

///
newring=(R,H)->(
--make a new ring from a ring R, with just one set of variables,
--same degrees as the degrees of R, and a heft vector as given.
     D:=last degrees vars R;
--     print D;
--     error();
     n:=length D;
     kkk:=coefficientRing R;
     RRR:=kkk[W_0..W_(n-1),Degrees=>D, Heft=>H];
     (RRR, map(RRR,R, vars RRR)))

newring1=(R,t)->(
--make a new ring from a ring R, with just one set of variables,
--of which the first t have degree 1,0 and, and are called X, and the last have degree 0,1
--and are called Y.
     D:=toList((t:{1,0})|((numgens R-t):{0,1}));
--     print D;
--     error();
     n:=length D;
     kkk:=coefficientRing R;
--Do we need the next line?
--     X:= symbol X; Y:=symbol Y;
     RRR:=kkk[X_0..X_(t-1),Y_0..Y_(n-t-1),Degrees=>D, Heft=>{1,1}];
     (RRR, map(RRR,R, (vars RRR)_{t..n-1}|(vars RRR)_{0..t-1})))

reesIdeal1 = I -> (
     S:=ring I;
     numOld:=numgens S;
     IR:=reesIdeal I;
     (newring1(ring IR, numOld))_1 IR
     )

///
restart
load "reesRegs.m2"
kk=ZZ/101
S=kk[x,y]
i = ideal"x3, x2y, y3"
--I=reesIdeal i
I=reesIdeal1 i
degrees vars ring I
use ring I
RI = (ring I)^1/I
regularity(RI, Weights=> {0,1})
regularity((ideal(X_0,X_1))*RI, Weights=>{0,1})
regularity((ideal(X_0,X_1))^2*RI, Weights=>{0,1})
regularity((ideal(X_0,X_1))^22*RI, Weights=>{1,0})
FF=res((ideal(X_0,X_1))^0*RI)
FF=res((ideal(X_0,X_1))^1*RI)
FF=res((ideal(X_0,X_1))^2*RI)
FF.dd
viewHelp regularity
///
     
  

yReesRegularity = method()
yReesRegularity Ideal := (I) -> (
     L := reesIdeal(I,I_0);
     (RRR,f):=newring(ring I, {1,1});
     print degrees vars ring L;
     newI:= f L;
     regularity betti (res newI, Weights=>{1,0}))

xReesRegularity = method()
xReesRegularity Ideal := (I) -> (
     L := reesIdeal(I,I_0);
     regularity betti (res L, Weights=>{1,0}))

yRR = yReesRegularity  
xRR = xReesRegularity     

ratliffRush = i ->(
     yr:=YRR i;
     for t from 1 to 2*yr do (
     print last degrees mingens (i^(t+1):i^t))
     )
///
restart
load "reesRegs.m2"
S=kk[x,y]
i=ideal"x20,y4x16, x4y16,xy4"
ratliffRush i
regfunction i
i=ideal(x^20,y^20,x^3*y^17,x^12*y^8)
i=ideal(x^20,y^20,x^3*y^17,x^15*y^5)
///


regfunction = (i) -> (
     yr:=YRR i;
     bBound := max(1,yr);
     r0:=regularity i^bBound;
     r1:=regularity i^(bBound+1);
     d:= r1-r0;
     e:= r0-bBound*d;
--     print("y-reg, d, e");
--     for t from 1 to max(1,bBound) do print (t, regularity i^t-d*t-e);
     t:=max(1,bBound-e);
     if regularity i^t =!= d*t+e then (
          print (bBound,d,e);
     	  print toString i;
	  flag=false;
	  for s from t to bBound do(
	       if flag =!=true and (regularity i^s == s*d+e) then
	       (print s; flag = true))
--	  error("this is a counterexample to y-reg - e")
	  );
     use ring i)

regfunction1 = (i) -> (
     yr:=YRR i;
     bBound := max(1,yr);
     r0:=regularity i^bBound;
     r1:=regularity i^(bBound+1);
     d:= r1-r0;
     e:= r0-bBound*d;
     use ring i;
     (yr, d, e)
     )

stabilization = i->(
     yr:=YRR i;
     bBound := max(1,yr);
     r0:=regularity i^bBound;
     r1:=regularity i^(bBound+1);
     d:= r1-r0;
     e:= r0-bBound*d;
     j=1;
     while regularity i^j != d*j+e do j=j+1;
     j)

iExample= (d,a,b)->ideal(x^d,y^d, x^a*y^(d-a), x^b*y^(d-b))
///
restart
load "reesRegs.m2"
kk=ZZ/101
S=kk[x,y]

stabilization (i= iExample(10,2,5))
regfunctionPrint i
regularity i

i=iExample(5,2,3)
regfunction i
d=20
for a from 1 to d-2 do(
     for b from a+1 to d-1 do(
	  regfunction iExample(d,a,b)
	  ))

i=iExample(10,2,8)
for t from 1 to 5 do print regularity i^t
for t from 0 to 10 do print betti res push(i,t)
i=iExample(20,4,16)
i=iExample(5,1,4)
regfunctionPrint i

regfunctionPrint i
for t from 1 to 5 do print regularity i^t
for t from 10 to 20 do print betti res push(i,t)
<<i
viewHelp "<<"
toString i
///     


///
--computing d
restart
load "reesRegs.m2"
kk=ZZ/101
S=kk[x,y]
iExample= (d,a,b)->ideal(x^d,y^d, x^a*y^(d-a), x^b*y^(d-b))
M=module ideal "x3, x2y6+y8, xy7"
i=iExample (7,1,5)+iExample(6,2,3)
u=i_0
orderedMinGens i
assymptoticDegree i
assymptoticDegree(i,M,u)

reesModule = method(Options => {Variable => w})
reesModule(Ideal, Module, RingElement):=:= Module => o -> (i,M,u) -> (
     R:= ring M;
     if R =!= ring u;
     then error("Expected Module and Element over the same ring");   
     P := presentation i;
     sourceDegs := apply(degrees target P, i -> prepend(1,i));
     RSourceTemp:=(coefficientRing R)(monoid[w_1..w_(rank target P)]**monoid R);
     RSource:=newRing(RSourceTemp, 
	  Degrees=>join(sourceDegs,drop ( (monoid RSourceTemp).Options.Degrees, rank target P)));
     NewVars:=matrix{apply(rank target P, i->RSource_i)};
     I := (NewVars*(substitute(P, RSource)));
     a = substitute(a, RSource);
     NewM:= substitute(M, Rsource);
     saturate(kernel I**NewM,a)
     )

reesIdeal (Module, RingElement) := Ideal => o -> (M,a) -> (
     R:= ring M;
     if R =!= ring a 
     then error("Expected Module and Element over the same ring");   
     P := presentation M;
     sourceDegs := apply(degrees target P, i -> prepend(1,i));
     RSourceTemp:=(coefficientRing R)(monoid[w_1..w_(rank target P)]**monoid R);
     RSource:=newRing(RSourceTemp, 
	  Degrees=>join(sourceDegs,drop ( (monoid RSourceTemp).Options.Degrees, rank target P)));
     NewVars:=matrix{apply(rank target P, i->RSource_i)};
     I := ideal (NewVars*(substitute(P, RSource)));
     a = substitute(a, RSource);
     saturate(I,a)
     )

reesIdeal(Ideal, RingElement) := Ideal => o -> (I,a) -> (
     reesIdeal(module I, a)
     )
     

///

orderedMinGens = i-> sort(mingens i, DegreeOrder=>Ascending)


assymptoticDegree = method()
assymptoticDegree(Ideal, Module, RingElement) := (i,M,u) ->(
     --takes an ideal and a module over a polynomial ring, returns the
     --assymptotic degree of the generators of the module on the ideal.
     --Here u should be an element of i that is outside each minimal prime of M.
     igens := orderedMinGens i;
     A:= annihilator M;
     R:=(ring i)/A;
     jgens := substitute(igens,R);
     I:=reesIdeal(ideal igens, u);
     xVars:=ideal substitute(vars ring i, ring I) ;
     J:=mingens(I+xVars);
     T:=(ring I)/ideal J;
     s:=dim T-1;
     ti:=ideal((vars T)_{0..s});
     while (dim (T/ti))>0 do (
     	  s=s+1;
	  ti=ti+ideal(T_s));
     print s;
     degree igens_s
     )
assymptoticDegree(Ideal):= i -> assymptoticDegree(i, (ring i)^1, i_0)


///
--Do the e's decrease in the case of powers of an m-primary ideal
--NOT generated in one degree? They seem to...
restart
load "reesRegs.m2"
iExample= (d,a,b)->ideal(x^d,y^d, x^a*y^(d-a), x^b*y^(d-b))
kk=ZZ/101
n=3
S=kk[x_1..x_n]
iBad = (d,k)->ideal (vars S)^[d]+(ideal vars S)^(d+k)
for d from 2 to 7 do(
     for k from 1 to d-1 do(
	  i=iBad(d,k);
	  for t from 1 to 5 do( --if k=!=(regularity i^t)-t*d then(
	       print (d,k,(regularity i^t)-t*d))))

--if n=2 then e_t = k all d,k,t     
d=4
k=1
i= ideal(vars S)^[d]+(ideal vars S)^(d+k)
for t from 1 to n+1 do print(t, regularity i^t - d*t, y

iExample= (d,a,b)->ideal(x^d,y^d, x^a*y^(d-a), x^b*y^(d-b))
d=30
i=iExample(d,1,d-1)+ideal(x^(d//2)*y^(d-(d//2)+4))

for d1 from 5 to 10 do (print d1;
     for d2 from d1 to 15 do (
	  for a from 1 to d1 do (
	       for b from 1 to d2 do (
		    i=ideal(x^d1, y^d2, x^a*y^b);
		    r0= 0;
		    d=d2;
		    for t from 1 to 15 do (
     			 r1 = (regularity i^t) - t*d;
     			 if (r1>r0 and t>1) then (print i; error("counterexample to descending"));
     			 r0 = r1)
		    ))))
i = iExample(10,2,8)+(ideal vars S)^16
for t from 1 to 7 do print ((regularity i^t)-10*t)


kk=ZZ/101
S=kk[x,y]
i=ideal(x^20,y^20, x^18*y^2,x^2*y^18)+(ideal(x,y))^27
for t from 1 to 10 do print ((regularity i^t)-20*t)

restart
--test the regularity?
reg1 = i-> (
     mm:=ideal vars ring i;
     r:= min flatten degrees  i;
     g:=gb i;
     while ((gens mm^r) % g) != 0 do (print r; r=r+1);
     r  
    ) 

kk=ZZ/101
S=kk[x,y,z]
mm=ideal vars S
d=6
i=ideal (vars S)^[d]+(ideal vars S)^(d+1)
time reg1 i^5
time regularity i^5
time gb i^5 --97 sec
restart
time res i^5 --62 sec

restart
--what is the fiber ring of a reg seq (of degree d) plus socle?
S=kk[x,y,z]
f1=y^2-x*(x-1)*(x-2)
F1=homogenize(f1,z)
f2=y^2-x*(x-1)*(x-2)
F2=homogenize(f1,z)
f3=y^2-x*(x-1)*(x-2)
F3=homogenize(f1,z)
viewHelp homogenize
///


YRR= i->(
iR=reesIdeal(i,i_0);
(RRR, f)=newring(ring iR,{1,1});
newI= f iR;
regularity betti (res newI, Weights=>{1,0})
)

randomFromIdeal=(I, d, n) ->(
     --returns ideal generated by n random elements of degree d from an ideal I
     f:=gens I;
     g=random(source f, S^{n:-d});
     ideal(f*g)
     )

push = (i,e)->(
     --takes an m-primary ideal i generated in a single degree in a polynomial ring S
     --and a positive integer e. Forms a polynomial ring T whose generators (which have deg 1)
     --correspond to the generators of i. 
     --returns the module over T generated by the forms of degree e in S.
S:=ring i;
T1:=kk[A_1..A_(numgens i),Degrees=>last degrees gens i];
F:=map(S,T1,gens i);
Ne:=presentation pushForward(F,module((ideal vars S)^e));
n:=numgens ((ideal vars S)^e);
Me:=transpose (sort(transpose Ne,DegreeOrder=>Descending));
T:=kk[A_1..A_(numgens i)];
f:=map(T,T1);
M= f Me;
p=map(target M, T^{n:-e},(i,j)->if i==j and i<=n-1 then 1_T else 0_T);
q=map(target M, target M, (i,j) -> if i==j and i>=n then 1_T else 0_T);
minPres( (target M)/((intersect(image p, image M))+(image q)))
)     

h1Reg=i->(
     --compute the degrees of the generators of
     --(x)*(y) socle of H_(y)^1 of the Rees algebra,
     --and perhaps also the H^1 module presentation.
     iR:=reesIdeal(i,i_0);
     (RRR, f):=newring1(ring iR,numgens i);
     newI:= f iR;
     --the y-variables
     n:=ideal (RRR_0..RRR_((numgens i) -1));
     --the x variables
     m:=ideal (RRR_(numgens i)..RRR_((numgens RRR) -1));
     --print the bidegrees of the socle generators. second degrees are the x, first are the y.
    s:=last degrees mingens (((newI+ideal(RRR_0)):(n))/(newI+ideal(RRR_0)));
    g:=last degrees mingens (saturate((newI+ideal(RRR_0)),n)/(newI+ideal(RRR_0)));
--     print s;
     os = organize s;
     og = organize g;
     print organize s;
--     print g;
     print organize g;     
     print("");
--     if not (testFirstDecreasing os and testFirstDecreasing og) then(
     if not (testFirstDecreasing og) then(
   	  print i; error("counterexample"));
     (s, g))

organize = s ->(
     --s is a llist of lists {a,b}. function returns a list of pairs
     --whose first elements are the maximum a for each b, followed by b,
     --in increasing order of b.
     lasts =unique sort( for t from 0 to #s-1 list (last s_t));
     start = min lasts;
     stop = max lasts;
     for t from 0 to #lasts-1 list(
	  st:=select(s, p-> last p == lasts_t);
	  stmax:=max (for u from 0 to #st-1 list first st_u);
	  {stmax, lasts_t})
     )

testFirstDecreasing= L ->(
     -- for a list of lists {a,b}, tests whether 
     --the sequence of a's is weakly decreasing.
     v:= true;
     for t from 0 to #L-2 do(
	  if first(L_(t+1))>first(L_t) then v=false);
     v)
regularities = i->(
--     s:=stabilization i;
     e:=(regfunction1 i)_2;
     for t from 1 to e list(
     M0=push(i,t);
     R:=ring M0;
     R0:=R/ideal(R_0);
     f:=map(R0^(numgens i),R0^{-1}, transpose vars R0);
     r:=(regularity M0)-t;
     K:=kernel(f**(R0**M0));
     {r,max (flatten last degrees mingens K)-t-1}
     )
)
///
restart
load "reesRegs.m2"
S=kk[x,y]
for d from 5 to 14 do(
time for a from 1 to d//2 do(
     for b from a+1 to d-1 do(
	  L=regularities  iExample(d,a,b);
	  if not  (isDecreasing (L/first) and isDecreasing (L/last)) then (
	       print("the following is a counterexample"));
	       print(d,a,b);
	       for t from 0 to length L -1 do (
		    if last L_t != -infinity and first L_t != last L_t then print(L));
	  )))

d=10;d1=5
i=ideal(x^d)+ (ideal vars S)^(d-d1)*ideal(y^d1)
regularities i


regfunction1 iExample(20,4,16)     
regularities iExample(20,4,16)

i=iExample(20,2,15)
(s,g)=h1Reg i
organize s
organize g
s
t=0
for t from 0 to 10 do (


0_M0:ideal vars R0
vars R0
regfunctionPrint i
for t from 0 to 10 do print regularity push(i,t),
--the regularity of N_i is  decreasing, 
--BUT the  regularity of H^1 is NOT.
--nevertheless the h1-regularity of N_0 is the biggest.

///

isDecreasing = L-> (
     v:=true;
     for i from 1 to length L - 1 do(
	  if L_i>L_(i-1) then v=false);
     v)

///
--check whether the regularity of push(i,e) is decreasing with e
--Always in the case of primary ideals generated in a single degree d.
--We KNOW this is the case starting with e = \epsilon, the
--assymptotic excess regularity, so we only need to check up to there.
--Note that push(i,0) is the regularity of the ring k[i_d], which in
--this case is the fiber ring.
restart
load "reesRegs.m2"
--load "randomIdeal.m2"
--viewHelp "<<"
pushCheck= i ->(
     d:=(degree i_0)_0;
     yr:=YRR i;
--     <<"YRegularity="<<yr;
     eps:=regularity i^yr - yr*d ;
--     <<", epsilon="<<eps <<endl;
     r0:=regularity push(i,0);
     for e from 1 to eps do(
     	  r1:=regularity push(i,e)-e;
	  if r1>r0 then (
	       print i;
	       print yr;
	       print eps;
	       error("counterexemample found!"))
	  else r0= r1)
     )

pushCheck1= i ->(
     d:=(degree i_0)_0;
     yr:=YRR i;
--     <<"YRegularity="<<yr;
     eps:=regularity i^yr - yr*d ;
--     <<", epsilon="<<eps <<endl;
     L:=(for e from 0 to eps list(
     	  regularity push(i,e)-e));
    print L;
     if isDecreasing L == false then (
	  print i;
	  error("counterexample!"));
     L
     )
	  
isDecreasing( {3,1,2})

kk=ZZ/101
S=kk[x,y]
i=ideal"x4,x3y,  y4"
pushCheck1 i
pushCheck i

i=ideal"x20,y20,x16y4,x4y16"
i=ideal"x20,y20,x18y2,x2y18"
pushCheck1 i

test=(n,d,N)->(
     --test N binomial ideals of degree d in n variables
     R=ZZ/101[Z_1..Z_n];
     for t from 1 to N list(
	  i=ideal(0_R); 
	  while (codim i) < n do(
          i=randomBinomialPrimaryIdeal(d,R,1+random(2));
	  );
     pushCheck1 i)
)
S=kk[x,y,z]
tally test(3,4,100)

d=4
S=kk[x,y,z]
i0=(ideal vars S)^[d]


time for t from 1 to 10 do pushCheck(i0+randomMonomialIdeal(S,d,1))

///

purePowers=(d,S)->for t from 0 to numgens S - 1 list (S_t)^d
impure=(d,S)->(
     c:=compress(basis(d,S)%map(S^1,S^{numgens S:-d}, matrix{purePowers(d,S)}));
     for i from 0 to rank source c -1 list c_(0,i))
     

randomBinomialPrimaryIdeal=(d,S,g)->(
     --numgens+g generators; the first chosen with a pure power as half.
     kk=coefficientRing S;
     P:=purePowers(d,S);
     Q:=impure(d,S);
     m:=length Q;
     L:=for t from 0 to numgens S-1 list P_t-(random kk)*Q_(random (m-1));
     L1:=for t from 1 to g list Q_(random (m-1))-(random kk)*Q_(random (m-1));
     ideal mingens ideal(L|L1))

randomPrimaryIdeal=(d,S,g1,g2)->(
     --numgens+g1+g2 generators; the first numgens chosen to be d-th powers of the variables.
     --g1= number of monomials other than the powers
     --g2= number of binomials.
     kk:=coefficientRing S;
     P:=purePowers(d,S);
     Q:=impure(d,S);
     m:=length Q;
     h:=0;
     L:=for t from 1 to g1 list Q_(random (m-1));
     L1:=for t from 1 to g2 list Q_(random (m-1))-(random kk)*Q_(random (m-1));
     ideal mingens ideal(P)+ideal(L|L1)
     )

///
restart
load "reesRegs.m2"
kk=ZZ/101
S=kk[x,y,z]

for t from 1 to 100 do(
I=randomPrimaryIdeal(3,S,2,0);
print (L:=regularities I);
for u from 0 to #L-1 do(
     if (last(L_u) != -infinity and last (L_u) != first (L_u)) then(
	  print  toString I);
     )
)

S=kk[x,y,z]

for d from 2 to 5 do(
i = (ideal vars S)^d;
for t from 0 to 5 do print (regularity push(i,t)-t);
print("");)


i=ideal(w^3,z^3,y^3,x^3,x*z*w,y^2*w)
i=ideal(w^3,z^3,y^3,x^3,y*z^2,x*w^2)

betti res push(i,3)
betti res M



entry=(d,e)->(
i=(ideal vars S)^d;
M=push(i,e);
regularity push(i,e)
)
n=3
entry1=(d,e)->(
   ((max(d-1, n*(d-1)-e))//d)+e)
entry1(3,4)
map(ZZ^10, ZZ^10, (d1,e)->entry1(d1+1,e))

S=kk[x,y]
map(ZZ^10, ZZ^10, (d1,e)->entry(d1+1,e))
o39 = | 0 1 2 3 4 5 6 7 8 9 |
      | 1 1 2 3 4 5 6 7 8 9 |
      | 1 2 2 3 4 5 6 7 8 9 |
      | 1 2 3 3 4 5 6 7 8 9 |
      | 1 2 3 4 4 5 6 7 8 9 |
      | 1 2 3 4 5 5 6 7 8 9 |
      | 1 2 3 4 5 6 6 7 8 9 |
      | 1 2 3 4 5 6 7 7 8 9 |
      | 1 2 3 4 5 6 7 8 8 9 |
      | 1 2 3 4 5 6 7 8 9 9 |

S=kk[x,y,z]
--map(ZZ^3, ZZ^8, (d1,e)->entry(d1+1,e))
o6 = | 0 1 2 3 4 5 6 7 |
     | 1 2 2 3 4 5 6 7 |
     | 2 2 3 4 4 5 6 7 |

entry(4,0)--2
entry(4,1)
restart
load "reesRegs.m2"
kk=ZZ/101
S=kk[x,y]
i=ideal"x4, xy3,y4"
Me= push(i,2)
regfunction i
for e from 0 to 7 do print (regularity push(i,e))

X=map(S^{0,-1},S^0,matrix{{};{}})


load "reesRegs.m2"
kk=ZZ/101
S=kk[x,y,z]
i=ideal "x4,x3y,x3z, y4,z4, z3y"
d=5
i=ideal(x^d,x^(d-1)*y, x^(d-1)*z, y^d, z^d, z^(d-1)*x, z^(d-1)*y,x^(d//3)*y^(d//3)*z^(d-2*(d//3)))
i=ideal(x^d,x^(d-1)*y, x^(d-1)*z, y^d, z^d, z^(d-1)*x, z^(d-1)*y)
regfunction i
for t from 1 to 5 do print  regularity i^t
for e from 0 to 9 do print (e, regularity push(i,e))

restart
load "reesRegs.m2"
kk=ZZ/101
S=kk[a,b,c,d]
i2=ideal(vars S)^[2]
j=ideal"ab,ac,ad"
i=i2+j
i=i2
regfunction i
for t from 1 to 5 do print  regularity i^t
for e from 0 to 9 do print (e, regularity push(i,e))


///


--given 
--a polynomial ring S, with ideal I
-- primary to the maximal ideal M (note: the number of vars doesn't occur!)
--d= degree of all the generators of I
--E the sequence of assymptotic degrees of I, that is,
--e_p=E_(p+1) where reg I^p = dp+e_p
--k a positive integer,
--The program outputs a list of the assymptotic degrees of 
--I+M^(d+k). 
--The same number of values are output as are given in L.
eList=method()
eList(ZZ,List,ZZ) := (d,E,k) ->(
     e:=p->E_(p-1);
     P0:=for l from 1 to #E list (p=1;
	  while d*p+e(p)<(d+k)*l-k*p do p=p+1;
	  p);
     p0:=l->P0_(l-1);
     for i from 1 to #E list min(d*p0(i)+e(p0(i)), (d+k)*i - k*(p0(i)-1))-d*i
     )

///
restart
load "reesRegs.m2"
E = {12, 12, 12, 12}
eList(5,E,1)

--example of a regular sequence of n forms of degree d plus m^(d+k).
--len = length of output desired.
eListRegSeq=(n,d,len) -> for i from 1 to len list (n-1)*(d-1)
exRegSeq=(n,d,k,len)->eList(d,eListRegSeq(n,d,len),k)
exRegSeq(7,9,1,10)

--example where I has eList = L, and we output the eList of IM^t
eListIMt=(L,t) -> for i from 1 to #L list max(0,L_(i-1)-t*i)
eListRegSeq(5,5,10)
eListIMt(eListRegSeq(5,5,10),1)

--and now add the next power of M:
eList(5,eListIMt(eListRegSeq(4,4,10),1),1)

eList(6,7,{12,12,12,12,12}, 1)
///





end  
restart
kk=ZZ/101
S=kk[x,y]
Iexample=(a,b,c,d)->ideal(x^a, y^b, x^c*y^d)
a=11
b=10
for c from 2 to 10 do for d from 2 to 9 do (
     t=7;
     i=Iexample(a,b,c,d);
     print (a,b,c,d,"=>",max(a+d,b+c)-2-a+1==(regularity(i^t)) - t*a);
     print(d-1==(regularity(i^t)) - t*a)
)
i=Iexample(11,10,10,1)
for t from 1 to 10 do print regularity i^t
regfunction i
--Daffyd: 
restart
load "reesRegs.m2"
kk=ZZ/101
<
S=kk[x,y]
use S
i=ideal"x4,x3y, xy3,y4"
i=ideal"x4, xy3,y4"
i=ideal"x6, x4y2, xy5,y6"
i=ideal"x6,x4y2, xy5,y6"
d=4

kk=ZZ/101
S=kk[x,y,z]
i=ideal "x4,x3y,x3z, y4,z4, z3y"
d=6
i=ideal(x^d,x^(d-1)*y, x^(d-1)*z, y^d, z^d, z^(d-1)*x, z^(d-1)*y)
regfunction i
 for t from 1 to 5 do print  regularity i^t
randomFromIdeal(i,4,2)
(gens oo) % gb i

restart
load "reesRegs.m2"

kk=ZZ/101
S=kk[x,y]
for d from 4 to 15 do(
     use S;
     i1=ideal(x^(d//2));
     j1 = ideal product(1..(d//2), i->(x-i));
     m=ideal(x,y);
     print d;
--     print regfunction(i1*m^(d-(d//2))+ideal random(S^1,S^{-d}));
--     print regfunction(j1*m^(d-(d//2))+ideal random(S^1,S^{-d}));
     print regfunction(randomFromIdeal(i1,d,2)+ideal(y^d));	       
     use S;
     print regfunction(randomFromIdeal(j1,d,2)+ideal(y^d));  
     )


--in 2 variables, seems the worst we get is yreg-e, achieved by x^d, x^d-e-1, xy^d-1, y^d
kk=ZZ/101
S=kk[x,y,z]
i=ideal "x4,y4,z4,x2y2,x2z2,xy3,y2z2,yz3,xz3"
yr=YRR i
for m from 1 to yr+3 do print regularity i^m
iR=reesIdeal(i,i_0)
use ring iR
(RRR, f)=newring(ring iR,{1,1});
J=trim (iR+ideal(x,y,z))
K=f J
degrees vars RRR
betti (res (f J),Weights=>{1,0})

restart
load "reesRegs.m2"
kk=ZZ/101
n=3
S=kk[x_1..x_3]
use S
i=((ideal(x_1..x_2))^[3])*(ideal vars S)+ideal(random(S^1, S^{-4}))
betti res i
yr=YRR i
for m from 1 to yr+2  do print regularity i^m
 
iR=reesIdeal(i,i_0)
use ring iR
(RRR, f)=newring(ring iR,{1,1});
J=trim (iR+ideal(x,y,z))
K=f J
degrees vars RRR
betti (res (f J),Weights=>{1,0})


d=6
i=ideal random (S^1, S^{3:-d})
for m from 1 to yr+3 do print regularity i^m
yr=YRR i
--for 3 generic forms in 2 vars of deg d, we get y-regularity d-1, e is 1, stab is d-2.


I=reesIdeal(module i, i_0)
degrees vars ring I
yRR i

regfunction i
for t from 1 to 5 do print regularity(i^t)

yRR i

R=ZZ/101[a..e]
I=monomialCurveIdeal(R, {1,2,3,5})
RI=reesAlgebra(I)
degrees vars ring RI
S=ring RI
C=res RI
betti C

bBound = xRR I -- 
m=stabilizationBound I
regList = apply(1..m, i-> regularity(I^i))
a = regList#(m-1) -regList#(m-2)
b = apply(1..m-1, i-> regularity(I^i)-a*i)


I=monomialCurveIdeal(R, {1,2,3,6})
RI=reesAlgebra(I)
bBound = xRR I -- 
m=stabilizationBound I
regList = apply(1..m, i-> regularity(I^i))
a = regList#(m-1) -regList#(m-2)
b = apply(1..m-1, i-> regularity(I^i)-a*i)

--------------------------------

restart	  
load "reesRegs.m2"
kk=ZZ/101
--S=kk[x,y]
--

S=kk[x,y]
I=ideal"x6,y11,x5y10"
RI=reesAlgebra(I)
bBound = xRR I -- 
m=stabilizationBound I
regList = apply(1..10, i-> regularity(I^i))
a = regList#(m) -regList#(m-1)
b = apply(1..m-1, i-> regularity(I^i)-a*i)


R=ZZ/101[x,y,u,v]
d=3
test = d -> ( 
I := ideal(x^d, y^d, u^(d-1)*x-v^(d-1)*y);
-- regularity(I)
RI := reesAlgebra(I);
S := ring RI;
weightedBetti(betti res RI,{0,1});
print (stabilize := maxTwist weightedBetti(betti res RI, {0,1}));
print (bBound := xRR I - 1) ; 
regList := apply(stabilize, i-> regularity(I^i));
print (apply(length(regList)-1, i -> regList#(i+1)-regList#i)); 
print "a="; print (a := regList#(stabilize-1) -regList#(stabilize-2));
print (remList = apply(stabilize, i-> regularity(I^i)-a*i));
print (b := last remList);
)
test 3


--------- Oct 18 2008
--test pure powers plus power of the max ideal.
restart
load "reesRegs.m2"
kk=ZZ/101
n=4
S=kk[x_1..x_n]
d=5
k=1
test=(d,k,m)->(
--     i1=(ideal vars S)^[d];
     i1=(ideal vars S)*(ideal vars S)^[d-1];     
     i2=(ideal vars S)^(d+k);
          i=trim(i1+i2);
--       i=trim((ideal vars S)*i1);
for s from 1 to m do print ((time regularity i^s)-s*(d)))
--n*(c-1)+1
i
betti i
YRR i
test(5,1,5)

------------
-- and ideal where gr is CM, but the assympt gen degree (=3) is not the max deg of a gen.
--note that the assymp excess regularity is constant
S=kk[x,y]
i=ideal"x3,y3,x2y2"


for p from 1 to 6 do print(( regularity i^p) - 3*p)

---
--random monomial ideals in 2 variables:
restart
load "randomIdeal.m2"
kk=ZZ/101

diffs=L->(
     for i from 1 to #L-1 list L_(i-1)-L_i)
isDecreasing=L->(val:=true;
     for i from 1 to #L-1 do if L_(i-1)<L_i then val=false;
     val)
S=kk[x,y,z]
d=10
k=25
B=flatten entries gens (ideal(gens S))^d;
     for j from 1 to 100 do(
     i1=randomSparseIdeal(B, 1, k);
     i=trim ((ideal vars S)*ideal(vars S)^[d-1])+i1;
     t1 = isDecreasing (L=for m from 1 to 5 list (regularity(i^m) - m*d));
     t2= isDecreasing (L1=diffs L);
     if not (t1 and t2) then(
     	   print toString i);
      print(L,L1))



i=ideal"z10,xy2z7, x3z7, x4z6, y6z4, x6y3z, x7y2z,y10, xy9, x3y7, x10"

i = ideal"y20, x20,x2y18,x9y11,x17y3"
(L=for m from 1 to 5 list (regularity(i^m) - m*d))


------------
restart
load "ReesAlgebra.m2"     
S=ZZ/101[x,y,z]
i=trim((ideal vars S)^[4]+(ideal vars S)^5)
-- for m from 1 to 4 do print regularity i^m
-- 1,2,2,...
--what's the depth of the graded ring?
G=normalCone i;
degrees vars G
kernel map(G^1, G^{{-1,-4}},matrix{{w_1}})
--this is zero, so depth is at least 1. Seems not to be 2.


S=ZZ/101[x,y,z,w]
i=trim((ideal vars S)*(ideal vars S)^[4]+(ideal vars S)^6)
for m from 1 to 4 do print regularity i^m
-- 1,2,2,1,...
--what's the depth of the graded ring?
G=normalCone (i,x);
degrees vars G
kernel map(G^1, G^{{-1,-4}},matrix{{w_1}})
--this is zero, so depth is at least 1. Seems not to be 2.


restart
S=kk[x_0..x_4]
I=ideal random(S^1, S^{2:-3})
R=S/I
i=ideal(x_1..x_4)
j=reesIdeal(i, x_1)

regularity(j, Weights=>splice toList(5:{0},4:{1}))


restart
load "reesRegs.m2"
n=3
S=kk[x_0..x_n]
I=ideal (sum(0..n, i->x_i^3)+x_0*x_1*x_2, sum(0..n, i->(x_i-(i-i+1)*x_((i+1)%(n+1)))^3))
codim singularLocus I
R=S/I
i=ideal(x_1..x_n)
j=reesIdeal(i, x_0)

regularity(j, Weights=>splice toList((n+1):{0},n:{1}))
FF=res j
regularity(FF, Weights=>splice toList(n:1,(n+1):0))
vars ring j

use R
k=presentation  normalCone i
GG=res coker k
regularity(GG, Weights=>splice toList(n:1,(n+1):{0}))

restart
load "ExampleIdeals.m2"
n=4
S=kk[x_0..x_n]
I=ideal (sum(0..n, i->x_i^3)+x_0*x_1*x_2, sum(0..n, i->(x_i-(i-i+1)*x_((i+1)%(n+1)))^3))
--I= minors(2, matrix{{x_0,x_1,x_2},{x_3,x_4,x_0+x_1}})
--I = minors(2,random(S^2, S^{-1,-1,-2}))
degree I
codim singularLocus I
R=S/I
i=ideal(x_1..x_n)
toMagma i
j=reesIdeal(i, x_0)
describe ring j
(T,f) = flattenRing (S[w_0..w_3])

jT=substitute(j,T)+substitute(I, T)
jT=trim jT
betti (jT, Weights =>{1,1})
FjT = res(jT)
betti(FjT, Weights =>{1,0})
regularity (jT, Weights =>{1,0})

---------------------
--Projection of the Veronese
restart
kk=ZZ/32003
S=kk[a..f,A..F]
m=genericSymmetricMatrix(S,a,3)
m
i=minors(2,m)
betti res i
betti i
j = trim i


S1 = kk[a..f]
j1=sub(j, S1)
V = S1/j1
T = kk[A..E]
--J=saturate ker map(V,T,random(V^1, V^{5:-1}))
J=saturate ker map(V,T,{a-d,a-f,b,c,e})
codim singularLocus J
betti res J -- 7 cubics, T/J has proj dim 4, regularity 2

--the form of the following resolution is interesting: it's Gorenstein.
--but this is of course not the Rees alg to take for the purpose of 
--considering the projection map.

loadPackage "ReesAlgebra"
RJ =reesIdeal(J, J_0)


degrees ring RJ
betti(FF=res RJ, Weights=>{1,0}) -- regularity of the Rees algebraJ = 2
--             0  1  2  3  4  5 6
--o20 = total: 1 15 35 42 35 15 1
--         -2: .  .  .  1  .  . .
--         -1: .  .  5  5  5  5 .
--          0: 1 10 25 30 25 10 1
--          1: .  5  5  5  5  . .
--          2: .  .  .  1  .  . .

--so the power we need to take to check the assymptotic regularity of
--a set of linear forms is 3


--now the right rees algebra:

W = T/J
L=ideal(random(W^1,W^{4:-1}))
RL = reesIdeal(L, L_0);
degrees ring RL
betti(FF=res RL, Weights=>{1,0}) -- regularity of the Rees algebra of L is 4.
--note that this is the degree of the special fiber.

m=ideal vars W
L4 =L^4;
gens (m^5)%L3 -- not zero, but m^6 is zero.
compress (gens(m^(4+2)) % (L^4)) == 0
for p from 8 to 12 do print (compress (gens(m^(p+1)) % (L^p)) == 0)

--Thus the projection from P4 to P3 of the Vero image has (colinear) triple points.





---------------------
--Projection of a complete intersection of three general cubics;
--what's the y-Rees reg?
restart
kk=ZZ/32003
S = kk[a..f]
J=ideal random(S^1, S^{3:-3});

loadPackage "ReesAlgebra"

W = S/J
L=ideal(random(W^1,W^{5:-1}))
RL = reesIdeal(L, L_0);
degrees ring RL
time FF=res RL
betti(FF,Weights=>{1,0}) -- regularity of the Rees algebra of L is 7 (ideal gens in y-deg 8)
             0  1  2   3  4  5 6 7
o10 = total: 1 15 60 105 94 43 9 1
         -3: .  .  .   .  1  2 1 .
         -2: .  .  .   5 11  7 1 .
         -1: .  . 11  30 31 17 1 .
          0: 1 12 31  40 31  2 . .
          1: .  .  6  15  .  . . 1
          2: .  1  6   .  .  . 6 .
          3: .  1  .   .  . 15 . .
          4: .  .  .   . 20  . . .
          5: .  .  .  15  .  . . .
          6: .  .  6   .  .  . . .
          7: .  1  .   .  .  . . .

L=ideal(random(W^1,W^{4:-1}))
RL = reesIdeal(L, L_0);
degrees ring RL
time FF=res RL
betti(FF,Weights=>{1,0}) -- regularity of the Rees algebra of L is 


m=ideal vars W
L3 =L^3
gens (m^4)%L3 -- not zero, but m^5 is zero.
compress (gens(m^(3+2)) % (L^3)) == 0
for p from 8 to 12 do print (compress (gens(m^(p+1)) % (L^p)) == 0)



