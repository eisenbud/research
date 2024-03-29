howLongLinear = FF -> (
     --if FF is a complex, the routine
     --returns the number of linear steps in FF AFTER the first
     --by comparing min degrees FF_1 and max degrees F_n.
     --Thus, if FF is the resolution of an ideal, the result
     --is 
     -- >=1 iff all the generators are in the same degree and
     -- >=2 iff the ideal has linear presentation.
     --Returns the Green-Lazarsfeld index of the
     --resolution of a quadratic ideal.
     m := min flatten degrees FF_1;
     n := 0;
     while m+n == max flatten degrees FF_(1+n) do n=n+1;
     n)

--routine to report for which degree I contains all square-free
--monomials of that degree
truncs = I-> (
     d:=min flatten degrees I;
     while 0 != compress (gens squareFree(d, ring I))%I do 
     	  d = d+1;
     d)

full=(m,d,S) ->(
     --returns the ideal of square-free monomials in S
     --of degree d and not dividing a monomial m
     I1=intersect(ideal fromDual matrix{{m}}, squareFree(d, S));
     trim ideal (gens I1 % ideal((vars S)^[2]))
     )
load "RandomIdeal.m2"
end

restart
load "090423-huneke.m2"     
rsf=randomSquareFreeMonomialIdeal

kk=ZZ/101
S=kk[vars(0..9)]

I = randomMonomialIdeal(5:2, S)
I = squareFree(3,S)
truncs I
betti (FF= res I)
howLongLinear FF

--With 10 variables there are 120 square-free monomials of degree 3.
--70 random ones are rarely lin pres (4/1000)
--80 random ones are frequently lin pres
--the following run of 1000 takes 26 seconds on DE's laptop (4/09).
time for p from 1 to 1000 do(
I=rsf(70:3,S);
F=res I;
if (l=howLongLinear F) >=2 then <<I <<endl <<l<<endl
)

time tally for p from 1 to 100 list(
I=rsf(90:3,S);
howLongLinear res I
)

I=ideal (f*g*h, c*d*j, a*g*j, a*g*i, c*f*h, b*f*j, a*e*h, b*g*h, b*c*i, b*c*e, b*h*i, a*e*g, c*e*g, b*f*g, c*e*j, d*f*i, c*f*g, c*f*j, b*f*i, b*e*f, c*e*h, a*e*f, d*f*g, a*c*h, d*g*j, c*h*j, e*f*j, a*b*d, a*g*h, b*e*h, a*f*g, d*h*i, a*h*i, a*b*g, d*e*g, a*c*f, a*d*f, c*d*f, d*f*h, b*c*h, e*f*h, b*c*d, b*c*g, a*c*e, b*d*j, c*h*i, c*g*i, b*g*i, a*e*j, b*c*f, c*e*f, c*d*g, c*d*i, d*f*j, a*d*h, c*g*j, b*d*h, a*f*i, b*d*f, b*d*e, g*h*j, b*g*j, f*g*j, a*i*j, d*g*h, a*b*j, c*g*h, a*e*i, c*d*h, b*d*g, b*c*j, b*f*h, a*c*i, e*f*i, a*b*i)
betti res I -- has linear presentation
truncs I -- contains squareFree(5,S), but not squareFree(4,S)

S=kk[a..f]
I=ideal (b*c, d*e, a*d, e*f, d*e) -- reg is 3 but does not contain all
--square-free mmonomials of degree 3. Is NOT linearly presented.
truncs oo

--For the following ideal, the regularity is 3, but the ideal
--doesn't contain the square-free's of degree 4, but does contain
--those of degree 5.
S=kk[a..f]
I=ideal (e*f, b*f, a*f, c*d, b*c)
betti res I
truncs I

S=kk[a..i]
J3=ideal(a*b*c,a*b*e,a*b*f,a*b*h,a*b*i,a*c*d,a*c*f,a*c*g,a*c*i,a*d*h,a*d*i,a*e*g,a*e*h,a*e*i,a*f*h,a*g*h,
        a*g*i,b*c*d,b*c*e,b*c*g,b*c*h,b*c*i,b*d*e,b*d*f,b*d*g,b*d*h,b*d*i,b*e*f,b*e*h,b*f*g,b*g*h,c*d*e,c*d*g,
        c*d*h,c*d*i,c*e*f,c*e*g,c*e*h,c*e*i,c*f*g,c*f*h,c*g*h,c*g*i,c*h*i,d*e*f,d*e*g,d*e*h,d*f*g,d*f*i,e*f*h,
        e*g*i,e*h*i,f*g*h,f*g*i,f*h*i)
truncs J3 == 5
-- has 2 steps linear res, reg = 4, but fails to contain dghi

S=kk[vars(0..9)]
I=ideal(a*b*c,a*b*d,a*b*e,a*b*f,a*b*i,a*c*d,a*c*e,a*c*g,a*c*h,a*c*i,a*d*g,a*d*h,a*e*f,a*e*g,a*e*h,a*e*i,
        a*f*g,a*f*h,a*f*j,a*g*i,a*h*i,a*h*j,a*i*j,b*c*d,b*c*e,b*c*f,b*c*h,b*d*e,b*d*f,b*d*h,b*d*i,b*e*g,b*e*i,
        b*e*j,b*f*h,b*f*i,b*f*j,b*g*i,b*g*j,b*h*i,b*h*j,c*d*g,c*d*h,c*d*i,c*d*j,c*e*f,c*e*g,c*e*i,c*e*j,c*f*g,
        c*f*h,c*f*i,c*f*j,c*g*i,c*g*j,c*h*i,c*h*j,c*i*j,d*e*f,d*e*g,d*e*h,d*e*i,d*e*j,d*f*g,d*f*h,d*f*i,d*f*j,
        d*g*h,d*g*i,d*g*j,d*h*i,d*i*j,e*f*h,e*f*j,e*g*h,e*g*i,e*h*i,e*h*j,e*i*j,f*g*i,f*h*i,f*i*j,g*h*i,g*h*j,
        g*i*j,h*i*j)
betti res I
truncs I == 5.
--this ideal has 4 steps linear resolution.

makeLinPresSquareFree = i -> (
     D=max flatten flatten degrees syz gens i;
     intersect(i, squareFree(D-1, ring i))
     )

S=kk[vars(0..8)]
for mm from 1 to 8 do(
     print mm;
     for nn from 1 to 100 do(
	  i = alexander randomSquareFreeMonomialIdeal(toList(10*mm:3), S);
	  j = makeLinPresSquareFree i;
	  F = res j;
	  if regularity F > D-1 then (
     	       << toString i <<endl;
     	       <<(betti F, betti res i) <<endl <<flush ;
     	  )
     )
     )

alexander = i -> (
     m2 = (ideal vars ring i)^[2];
     trim ideal (((gens(m2:i))%m2)))

betti res i
betti res alexander i
codim alexander i
regularity F
D
betti F
betti res j
