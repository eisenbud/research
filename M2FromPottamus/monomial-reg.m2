--load "simplicial.m2"

-- standardSimplex = method ()
-- standarSimplex Ring = (R)-> (
--      simplicialComplex(R/ideal diff(vars R,product((entries vars R)_0)))
--)



lcm2 = (f,g) -> (
     lift(f*g/gcd(f,g), ring f)
     )

lcm = (L) -> (
     R:=ring L_0;
     lcmL:=1_R;
     scan(L, k->(lcmL=lcm2(lcmL,k)));
     lcmL
     )

--Most efficient:
lcmM = (L) -> (
    m := intersect toSequence (L/(i -> monomialIdeal(i)));
    m_0)


lcmn = (n, sigma, L) -> (
     R := ring n;
     whereIssigma := apply(sigma, i-> position(L, j-> j==i));
     whereIsn := position(L, i-> i==n);
     SmallerMons := L_(select(whereIssigma, i-> whereIsn>=i));
     lcmSmallerMons := if #SmallerMons==0 then 1_R else lcmM(SmallerMons);
     lcmSmallerMonsRed := lcmSmallerMons//product(support lcmSmallerMons, i-> R_i);
     BiggerMons := L_(select(whereIssigma, i-> whereIsn<i));
     lcmBiggerMons := if #BiggerMons==0 then 1_R else lcmM(BiggerMons);
     lcmM({lcmSmallerMonsRed, lcmBiggerMons}))


lcmLarger = (n, sigma, L)  -> (
     R := ring n;
     whereIssigma := apply(sigma, i-> position(L, j-> j==i));
     whereIsn := position(L, i-> i==n);
     BiggerMons := L_(select(whereIssigma, i-> whereIsn<i));
     if #BiggerMons==0 then 1_R else lcmM(BiggerMons))
     
     

isSuperficial = method()
isSuperficial List := (L) -> (
     lt := #L;
     R := ring L_0; 
     all(1..lt-1, i-> (previous:=lcmM(take(L,i)); (previous//product(support previous, i-> R_i))//(L_i)==0_R))
     )
     
 
 
conditionP = method()
conditionP (ZZ, List) := (d,L) -> (
     allpossible := subsets(L,d+1);
     select(allpossible, sigma -> all(L, n -> (lcmn(n, sigma, L)//n == 0)))
     )


conditionL = method()
conditionL (ZZ,List) := (d,L) -> (
     allpossible := subsets(L,d+1);
     select(allpossible, sigma -> all(L, n -> (lcmLarger(n, sigma, L)//n == 0)))
     )
     


-- conditionP = method()
-- conditionP (ZZ, List) := (d,L) -> (
--     lt := #L-1;
--     allpossible := subsets(0..lt,d+1);
--     select(allpossible, sigma-> all(L, n-> (lcmn(n, L_sigma ,L)//n == 0)))
--     )

end

load "monomial-reg.m2"
R=ZZ/101[x_0..x_4]
m=x_0^31*x_1*x_2^4*x_4*2
n=x_0*x_1
support m
mred=product(support m, i-> R_i)

L={x_0^2, x_0*x_1^2*x_2, x_1*x_3, x_2^2*x_3, x_4^3} 
isSuperficial(L)
lcmn(x_0*x_1*x_2, L,L)
conditionP(1,L)


L={x_0^2,x_0*x_1,x_1^2}
conditionP(1,L)

M={x_0^2, x_0*x_1^2, x_0*x_1}
isSuperficial(M)


R=ZZ/101[x,y,z]
L={x^2*z, x*y, y^2*z, z^2}
isSuperficial(L)
conditionP(1,L)


------------------------------------------------
R=ZZ/101[x,y,z]
L={x^2*z, x*y*z, y^2*z, x^3*y^5, x^4*y^4, x^5*y^3}
betti res ideal(L)


-------------------------------------------------
R=ZZ/101[x_1..x_6]
L={x_1*x_2, x_1*x_3, x_2*x_3, x_2*x_4, x_1*x_5, x_3*x_6}
I=ideal(L)
betti res I
isSuperficial(L)
conditionP(1,L)
apply(5, j-> #conditionP(j,L))


---------------------------------------------------------------------
--- The permutahedron
R=ZZ/101[x,y,z]
L={x*y^2*z^3, x*y^3*z^2, x^2*y*z^3, x^2*y^3*z, x^3*y*z^2, x^3*y^2*z} 
I=ideal(L)
betti res I
isSuperficial(L)
kel1=conditionP(1,L)
dPsyz1=apply(skel1, j-> lcmM(j))
skel2=conditionP(2,L)
dPsyz2=apply(skel2, j-> lcmM(j))
apply(5, j-> #conditionP(j,L))

skel1L=conditionL(1,L)
dLsyz1=apply(skel1L, j-> lcmM(j))
skel2L=conditionL(2,L)
dLsyz2=apply(skel2L, j-> lcmM(j))
apply(5, j-> #conditionL(j,L))
skel3L=conditionL(3,L)
dLsyz3=apply(skel3L, j-> lcmM(j))

select(skel1L, j-> not member(j,skel1))
select(skel2L, j-> not member(j,skel2))


-- Example 1: boundary of a tetrahedron
D = simplicialComplex {{0,1,2},{0,1,3},{0,2,3},{1,2,3}}
maxfaces D
dim D
nonfaces D
chainComplex D
bd(2,D)


///
