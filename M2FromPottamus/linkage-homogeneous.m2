 --HOPE: if the generic initial ideal is licci, then the ideal is licci
--Shake 'n Bake:
--although the licci ideal i does not link down to a ci by
--taking minimal regular sequences each time, it does if we
--start by taking a reg sequence of 3 elements 2 of which are in 
--the "second lowest degree of a complete intersection in i"

--a routine to find a regular sequence
--of smallest degrees in a homogeneous ideal.
smallestRegularSequence= i ->(
     icodim:=codim i;
     m:=gens i;
     L1:=flatten degrees source gens i;
     L:=sort unique L1;
     if L=!={0} then(
           f:=(gens i)*random(source gens i, S^{-L_0});
	   CI:=matrix{{f}};
	   c:=1;
	   j:=0;
          while (j<= #L-1  and c < icodim)
	    do(
	      n:=submatrix(m,{0},positions(L1, i->(i<=L_j)));
     	      if codim ideal n > c 
	        then (
 	          f=n*random(source n, S^{-L_j});
     	          CI= CI | f ;
	          c=c+1) 
	        else (j=j+1);
	      ))
            else CI=0;
	  CI
)

--the following returns the link of i by a regular sequence
--of minimal degrees among those inside i.
minLink= i->(
     j:=smallestRegularSequence i;
     print flatten degrees source j;
     quotient(ideal j,i)
     )

--the following returns the link of i by a regular sequence
--of almost minimal degrees among those inside i: that is, of
--degrees (d2,d2, d3, ... , dc), where (d1,d2,...,dc) is the
--list of minimal degrees of a regular sequence.
almostMinLink= i->(
     j:=smallestRegularSequence i;
     L:=flatten degrees source j;
     LL:=prepend (L#1,L_(toList(1..#L-1)));
     print LL;
     jj:=(gens i)*random(source gens i, S^-LL);
     quotient(ideal jj,i)
     )
end

restart
load "linkage-homogeneous.m2"

S=kk[x,y,z]

i=ideal(x^2*z, y^2*z, x^4,y^4,x*z^5, z^6,x*y*z^4)
betti res i

i1=almostMinLink i;
betti i1
i2=i1;
--repeat the next two lines over and over and see if you get a reg seq
i2=minLink i2
betti i2


