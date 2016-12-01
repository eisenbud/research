support = (m) -> (
-- support of a monomial
     n := numgens ring m;
     m = leadMonomial m;
     m = new List from m;
     m1 = select(m, k -> k#0 < n);
     apply(m1, k -> k#0))

lcm2 = (f,g) -> (
     lift(f*g/gcd(f,g), ring f)
     )

lcm = (L) -> (
     R:=ring L_0;
     lcmL:=1_R;
     scan(L, k->(lcmL=lcm2(lcmL,k)));
     lcmL
     )

-- lcm and lcm2 are really bad, especially for monomials

lcmM = (L) -> (
-- lcmM finds the lcm of a list of monomials; the quickest method we know
    m := intersect toSequence (L/(i -> monomialIdeal(i)));
    m_0)

--From now on,  n \in L, sigma \subset L, a list of monomials
lcmn = method()
lcmn (RingElement, List, List) := 
-- this computes the function lcm_n(sigma, L) from our draft
     (n, sigma, L) -> (
     R := ring n;
     whereIssigma := apply(sigma, i-> position(L, j-> j==i));
     whereIsn := position(L, i-> i==n);
     SmallerMons := L_(select(whereIssigma, i-> whereIsn>=i));
     lcmSmallerMons := if #SmallerMons==0 then 1_R else lcmM(SmallerMons);
     lcmSmallerMonsRed := lcmSmallerMons//product(support lcmSmallerMons, i-> R_i);
     BiggerMons := L_(select(whereIssigma, i-> whereIsn<i));
     lcmBiggerMons := if #BiggerMons==0 then 1_R else lcmM(BiggerMons);
     lcmM({lcmSmallerMonsRed, lcmBiggerMons}))

lcmLarger = method()
--If n \in L, sigma \subset L, then computes the the lcm of those elements of sigma that are later than n
lcmLarger (RingElement, List, List) := (n, sigma, L)  -> (
     R := ring n;
     whereIssigma := apply(sigma, i-> position(L, j-> j==i));
     whereIsn := position(L, i-> i==n);
     BiggerMons := L_(select(whereIssigma, i-> whereIsn<i));
     if #BiggerMons==0 then 1_R else lcmM(BiggerMons))
     
isSuperficial = method()
--checks whether a list is in superficial order (the last element not in the interior of the lcm of the previous etc;
--seems to be ok for reverse sort L for any list of monomials L
isSuperficial List := (L) -> (
     lt := #L;
     R := ring L_0; 
     all(1..lt-1, i-> (previous:=lcmM(take(L,i)); (previous//product(support previous, i-> R_i))//(L_i)==0_R))
     )
     
syzygiesP = method()
--produces the the sets  sigma of d+1 monomials of L that contribute to the P complex
syzygiesP (ZZ, List) := (d,L) -> (
     allpossible := subsets(L,d+1);
     select(allpossible, sigma -> all(L, n -> (lcmn(n, sigma, L)//n == 0)))
     )

--produces the the sets  sigma of d+1 monomials of L that contribute to the Lyubeznik complex
syzygiesL = method()
syzygiesL (ZZ,List) := (d,L) -> (
     allpossible := subsets(L,d+1);
     select(allpossible, sigma -> all(L, n -> (lcmLarger(n, sigma, L)//n == 0)))
     )
     

facesP = method()
--produces the the sets  sigma of d+1 of monomials of  L that contribute to the P complex     
facesP (ZZ, List) := (d,L) -> (
    lt := #L-1;
     allpossible := subsets(0..lt,d+1);
     select(allpossible, sigma-> all(L, n-> (lcmn(n, L_sigma ,L)//n == 0)))
     )

facesL = method()
--produces the the sets  sigma of d+1 of monomials of  L that contribute to the Lyubeznik complex     
facesL (ZZ,List) := (d,L) -> (
     lt := #L-1;
     allpossible := subsets(0..lt,d+1);
     select(allpossible, sigma -> all(L, n -> (lcmLarger(n, L_sigma, L)//n == 0)))
     )

Pres = L -> (
--finds the regularity of the P complex out to the number of variables
	  numvars := rank source vars ring L_0;
	              apply(numvars, i-> syzygiesP(i,L)))

Pbetti = L -> (
--finds the regularity of the P complex out to the number of variables
	  numvars := rank source vars ring L_0;
	       M := apply(numvars, i-> apply(syzygiesP(i,L), j-> lcmM(j))))
	

PbettiDegs = L -> (
--finds the regularity of the P complex out to the number of variables
	  numvars := rank source vars ring L_0;
	       M := apply(numvars, i-> apply(syzygiesP(i,L), j-> lcmM(j)));
	       N := apply(M, i->max flatten apply(i,j->degree j)))
	  

Preg = L -> (
--finds the regularity of the P complex out to the number of variables
	  numvars := rank source vars ring L_0;
	       M := apply(numvars, i-> apply(syzygiesP(i,L), j-> lcmM(j)));
	       N := apply(M, i->max flatten apply(i,j->degree j));
	       max apply(#N, i->N_i-i))

regi = I-> 1+ regularity coker gens I
--finds the regularity of an ideal I (regarded as a module)

listGens = I-> reverse sort (entries gens I)_0
--Lists the generators of I in revlex order (lexicographically biggest element, with
--resp to the reverse order of the vars, is last. This is a "superficial" order.

end

restart
path=path | {"/Users/de/Documents/M2/"}
load "Presolution-regularity.m2"
load "randomIdeal.m2"

kk=ZZ/32003
S1=kk[a,b,c, MonomialOrder=>GLex]
Ldegs ={2,3,4,5}
I1=randomMonomialIdeal(Ldegs, S1)
I1=(ideal vars S1)^3
L1=listGens trim I1
isSuperficial L1

S=kk[a,b,c]
L= apply(L1, i->substitute(i, S))
I=ideal L
regi I
Pr= Pres L
apply (Pr_1, i->print i)
Pbetti L
PbettiDegs L
Preg L


L={a^2,a*b,b^2}

