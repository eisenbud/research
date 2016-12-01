--Problem: compute the distinguished subvarieties and their
--"multiplicities" for an ideal I. Compare with the
--associated primes and their multiplicities.

--Is their an interpretation of the dist primes as, say,
--the primes that appear in an intersection product??
--of their "multiplicities"?

--The routines 

--distinguished
--distinguishedAndMult
--arithMults
--both

--are defined in "rees.m2"

--the following is only ok for monomial ideals!
restart
--load "monom.m2" 
--its loaded by my init.m2 file!
arithMults= i->(
     R:=ring i;
     L:=ass i;
     apply(L,
   G->(
   P=ideal G;
   X:=ideal vars R;
   fP:=map(R,R, apply(numgens X, 
	     i->if (X_i)%(gens P) ==0_R then X_i else 1_R));
   iP:=fP i;
   n:=numgens P;
   e:=degree Ext^n(R^1/iP,R);
   	       {e,P})))

both= i->(
     use ring i;
     print "arith mults";
     print arithMults i;
     use ring i;
     print "distinguished mults";
     print distinguishedAndMult i;
     )


load "rees.m2"
R=kk[x,y,z]
i=intersect(ideal(x),(ideal(x,y))^2, (ideal(x,y,z))^3)
both i
both ((ideal(x^2))*ideal(x,y,z))
distinguishedAndMult ((ideal(x^2))*ideal(x^3-y^2*z))
R=kk[x,y,z,w,u] 
distinguishedAndMult(minors(2,matrix{{x,y,z},{y,z,w},{z,w,u}}))

jr=randomMonIdeal(R,3,4)
both jr

R=kk[x,y,z]
j1=intersect(ideal(x), ideal(x^3,y))
use R
both j1

j2=intersect(ideal(x), ideal(x^2,x*y,y^2))
use R
both j2
d=3
use R
j3=(ideal(x,y))^d --the "distinguished mult" is d !
both j3
use R
j6=(ideal(x,y))*(ideal(y,z))
both j6
--NOT multiplicative
use R
j7=(ideal(x,y))*(ideal(y,z))*(ideal(z,x))
both j7 -- takes a while! But they come out the same!
use R
j8=intersect((ideal(x,y)),(ideal(y,z)),(ideal(z,x)))
both j8 -- not every dist prime is associated here
use R
j9=intersect((ideal(x,y)),(ideal(y,z)))
both j9 --no extra dist prime.

R=kk[x,y,z,w]
use R
j4=(ideal(x,y,z))*(ideal(y,z,w))
both j4
distinguishedAndMult j4
{{2, ideal (w, z, y, x)}, {1, ideal (z, y, x)}, {1, ideal (w, z, y)}}
--NOT multiplicative
use R
j5=intersect((ideal(x,y,z)),(ideal(y,z,w)))
distinguishedAndMult j5













