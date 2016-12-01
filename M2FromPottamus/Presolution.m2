support = (m) -> (
     n := numgens ring m;
     m = leadMonomial m;
     m = new Lis from m;
     m1 = select(m, k -> k#0 < n);
     apply(m1, k -> k#0))
 
-- support of a monomial


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
    m := intersect toSequence (L/(i -> monomialIdeal(i)));
    m_0)

-- lcmM does a quick job for monomials


lcmn = method()
lcmn (RingElement, List, List) := (n, sigma, L) -> (
     R := ring n;
     whereIssigma := apply(sigma, i-> position(L, j-> j==i));
     whereIsn := position(L, i-> i==n);
     SmallerMons := L_(select(whereIssigma, i-> whereIsn>=i));
     lcmSmallerMons := if #SmallerMons==0 then 1_R else lcmM(SmallerMons);
     lcmSmallerMonsRed := lcmSmallerMons//product(support lcmSmallerMons, i-> R_i);
     BiggerMons := L_(select(whereIssigma, i-> whereIsn<i));
     lcmBiggerMons := if #BiggerMons==0 then 1_R else lcmM(BiggerMons);
     lcmM({lcmSmallerMonsRed, lcmBiggerMons}))


-- this computes lcm_n from our draft

lcmLarger = method()
lcmLarger (RingElement, List, List) := (n, sigma, L)  -> (
     R := ring n;
     whereIssigma := apply(sigma, i-> position(L, j-> j==i));
     whereIsn := position(L, i-> i==n);
     BiggerMons := L_(select(whereIssigma, i-> whereIsn<i));
     if #BiggerMons==0 then 1_R else lcmM(BiggerMons))
     
-- lcmLarger computes the lcm of elements in sigma which are larger than n
     
isSuperficial = method()
isSuperficial List := (L) -> (
     lt := #L;
     R := ring L_0; 
     all(1..lt-1, i-> (previous:=lcmM(take(L,i)); (previous//product(support previous, i-> R_i))//(L_i)==0_R))
     )
     
 
 -- is Superficial cheks if a list is already superficially oredred
 
syzygiesP = method()
syzygiesP (ZZ, List) := (d,L) -> (
     allpossible := subsets(L,d+1);
     select(allpossible, sigma -> all(L, n -> (lcmn(n, sigma, L)//n == 0)))
     )


syzygiesL = method()
syzygiesL (ZZ,List) := (d,L) -> (
     allpossible := subsets(L,d+1);
     select(allpossible, sigma -> all(L, n -> (lcmLarger(n, sigma, L)//n == 0)))
     )
     
facesP = method()
facesP (ZZ, List) := (d,L) -> (
    lt := #L-1;
     allpossible := subsets(0..lt,d+1);
     select(allpossible, sigma-> all(L, n-> (lcmn(n, L_sigma ,L)//n == 0)))
     )


facesL = method()
facesL (ZZ,List) := (d,L) -> (
     lt := #L-1;
     allpossible := subsets(0..lt,d+1);
     select(allpossible, sigma -> all(L, n -> (lcmLarger(n, L_sigma, L)//n == 0)))
     )


Preg = L -> (
	  numvars := rank source vars ring L_0;
	       M := apply(numvars, i-> apply(syzygiesP(i,L), j-> lcmM(j)));
	       N := apply(M, i->max flatten apply(i,j->degree j));
	       max apply(#N, i->N_i-i))
regi = I-> 1+ regularity coker gens I

end

TEST///
restart
load "Presolution.m2"

---------------------------------------------------------------------
--- The permutahedron
x = symbol x
R=ZZ/101[x,y,z]
L={x*y^2*z^3, x*y^3*z^2, x^2*y*z^3, x^2*y^3*z, x^3*y*z^2, x^3*y^2*z} 
I=ideal(L)
betti res I
isSuperficial(L)
faces1=facesP(1,L)
skel1=syzygiesP(1,L) 
dPsyz1=apply(skel1, j-> lcmM(j))
faces2=facesP(2,L)
skel2=syzygiesP(2,L)
dPsyz2=apply(skel2, j-> lcmM(j))
apply(3, j-> #syzygiesP(j,L))

regi I
Preg L

skel1L=syzygiesL(1,L)
faces1L=facesL(1,L)
dLsyz1=apply(skel1L, j-> lcmM(j))
skel2L=syzygiesL(2,L)
faces2L=facesL(2,L)
dLsyz2=apply(skel2L, j-> lcmM(j))
apply(5, j-> #syzygiesL(j,L))
skel3L=syzygiesL(3,L)
faces3L=facesL(3,L)
dLsyz3=apply(skel3L, j-> lcmM(j))


-- computes next faces in Lyubeznik resolution not in the P resolution
select(skel1L, j-> not member(j,skel1))
select(faces1L, j -> not member(j,faces1))
select(skel2L, j-> not member(j,skel2))
select(faces2L, j -> not member(j,faces2))



///





-- this example is just testing the routines

R=ZZ/101[x_0..x_4]
m=x_0^31*x_1*x_2^4*x_4*2
support m
mred=product(support m, i-> R_i)
 
n=x_0*x_1
L={x_0^2, x_0*x_1^2*x_2, x_1*x_3, x_2^2*x_3, x_4^3} 
isSuperficial(L)
lcmn(x_0*x_1*x_2, L,L)
syzygiesP(1,L)
facesP(1,L)
facesL(1,L)



L={x_0^2,x_0*x_1,x_1^2}
syzygiesP(1,L)


-- M next is not superficial
M={x_0^2, x_0*x_1^2, x_0*x_1}
isSuperficial(M)

------------------------------------------------
x = symbol x
R=ZZ/101[x,y,z]
L={x^2*z, x*y, y^2*z, z^2}
isSuperficial(L)
syzygiesP(1,L)

------------------------------------------------
R=ZZ/101[x,y,z]
L={x^2*z, x*y*z, y^2*z, x^3*y^5, x^4*y^4, x^5*y^3}
betti res ideal(L)


-------------------------------------------------
-- A sqaurefree simple example
x = symbol x
R=ZZ/101[x_1..x_6]
L={x_1*x_2, x_1*x_3, x_2*x_3, x_2*x_4, x_1*x_5, x_3*x_6}
I=ideal(L)
betti res I
isSuperficial(L)
syzygiesP(1,L)
apply(5, j-> #syzygiesP(j,L))



