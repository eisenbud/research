

restart
--nodal curve in A^2
R = ZZ/32003[x,y,s,t,u,v,a,b]
f = x^2+x^3-y^2
jf = jacobian matrix {{f}}
tt = matrix{{s,t,u,v,a,b,0,0}}
f1 = tt*jf
jf1 = jacobian f1
f2 = tt*jf1
f3=tt*(jacobian f2)
j1 = ideal (f | f1)
j2 = ideal (f | f1 | f2)
j3 = ideal (f | f1 | f2 | f3)
S = ZZ/32003[x,y,s,t]
use R
A = R/j2
use A
phi = map(A,S,{x,y,s,t})
j21=ker phi
transpose gens j21
betti gens j21
use R
p=4*t^2*(1+x)-(2*s+3*x*s)^2
p^3%j2
p^2%j3
--p is nilpotent of order 3
x^2*p%j1

(gens(radical j2))%j2

--------------------
restart
--------------------
--cuspidal curve in A2
restart
R = ZZ/32003[x_0,y_0,x_1,y_1,x_2,y_2]
f = x_0^3-y_0^2
jf = jacobian matrix {{f}}
tt = matrix{{x_1,y_1,x_2,y_2,0,0}}
f1 = tt*jf
jf1 = jacobian f1
f2 = tt*jf1
f3=tt*(jacobian f2)
j1 = ideal (f | f1)
j2 = ideal (f | f1 | f2)
j3 = ideal (f | f1 | f2 | f3)

j1==radical j1
j1==j1:ideal(x_0,y_0)

j2==radical j2
j2==j2:ideal(x_0,y_0)


j3==j3:ideal(x_0,y_0)
j3 == radical j3
--------------------
quadric cone in A^3
restart
R = ZZ/32003[x_0,y_0,z_0,x_1,y_1,z_1,x_2,y_2,z_2]
f = x_0*y_0+z_0^2
jf = jacobian matrix {{f}}
tt = matrix{{x_1,y_1,z_1,x_2,y_2,z_2,0,0,0}}
f1 = tt*jf
jf1 = jacobian f1
f2 = tt*jf1
f3=tt*(jacobian f2)
j1 = ideal (f | f1)
j2 = ideal (f | f1 | f2)
j3 = ideal (f | f1 | f2 | f3)

j1==radical j1
j1==j1:ideal(x_0,y_0,z_0)

j2==radical j2
j2==j2:ideal(x_0,y_0,z_0)


j3==j3:ideal(x_0,y_0,z_0)
j3 == radical j3

------------------------------
--cone over elliptic plane curve
restart
R = ZZ/32003[x_0,y_0,z_0,x_1,y_1,z_1,x_2,y_2,z_2]
f = x_0^3+y_0^3+z_0^3
jf = jacobian matrix {{f}}
tt = matrix{{x_1,y_1,z_1,x_2,y_2,z_2,0,0,0}}
f1 = tt*jf
jf1 = jacobian f1
f2 = tt*jf1
j1 = ideal (f | f1)
j2 = ideal (f | f1 | f2)

j1==radical j1
j1==j1:ideal(x_0,y_0,z_0) --it is prime

--j2==radical j2 -- too hard!
P1=ideal(x_0,y_0, z_0)
j2==j2:P1 -- false, has components along P1

codim j2
--thus j2 is a regular sequence, no embedded components.

P=j2:(P1^5) -- this is the first saturated quotient, 
-- P is a prime.
betti P
Q1=j2:P -- this is saturated, j2:P^2 yields the same result

j2 == intersect(P,Q1)
--The primary decomposition!

6==degree Q1 -- the multiplicity.

transpose gens Q1

---------------------------------
--example as above; look at j3
restart
R = ZZ/32003[x_0,y_0,z_0,x_1,y_1,z_1,x_2,y_2,z_2,x_3,y_3,z_3]
f = x_0^3+y_0^3+z_0^3
jf = jacobian matrix {{f}}
tt = matrix{{x_1,y_1,z_1,x_2,y_2,z_2,x_3,y_3,z_3,0,0,0}}
f1 = tt*jf
f2 = tt*(jacobian f1)
f3 = tt*(jacobian f2)
j1 = ideal (f | f1)
j2 = ideal (f | f1 | f2)
j3 = ideal (f | f1 | f2 | f3)
P1=ideal(x_0,y_0, z_0) -- the possible bad locus

j3 == j3:P1 -- yields false
-- There are components supported over the singular
-- locus!

jets=(n,j)->(
     R:= ring j;
     numvars := numgens R;
     x :=quote x;
     RRR := ZZ/(char R)[x_{0,1}..x_{n,numvars}];
     f := map(RRR,R,(vars RRR)_{0..numvars-1});
     j0 := f(j);
     (vars RRR)_{numvars,...,n*numvars}
     )

