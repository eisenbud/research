--define the generic "cramer" map: given m: F\to G over a ring R and a number r (the rank), construct
--the "universal kernel" 
--c = \wedge^{r+1} F \otimes \wedge^r G* \to F.
--If G*\to F^* has  coker that is a first syz of finite pd, then m* is the kernel of c*. 
--This is true in general over a domain if the coker is torsion free
--(proof: localize at zero), but not for "torsionless" in general. 

orderedPairs = (L1, L2) -> (
     flatten apply(L1, i-> apply(L2,(j->{i,j})))
     )

--not used:
positionSign= (i,L) ->(
     if not member(i,L) then 0 else
     	  (p:=position(L, x -> x==i);
	   (-1)^p)
     )
       
cramer = (m,r) ->(
     p = rank source m;
     q = rank target m;
     R = ring m;
     T = orderedPairs(subsets(toList(0..q-1), r+1),subsets(toList(0..p-1), r));
     C = map(R^(binomial(q, r+1)*binomial(p,r)),target m, (i,j)-> (
	                 rows  = first (T_i);
	     	       	 cols = last (T_i);
			 if not member(j,rows) then 0_R else (
			 p = position(rows, x->x==j);
			 newRows = flatten{take(rows,{0,p-1}),take(rows,{p+1,#rows-1})};
			 (-1)^p*det(m_cols^newRows))
		    )
	       )
	  )
			 
end
restart
load "cramer-map.m2"

-- An example when R is a domain
R = kk[a..d]/ideal(a^2+b^2+c^2+d^2)
M = syz vars R
r=rank M
C = cramer(M,r);
Cr=chainComplex(C,M)
0==prune homology(1,Cr)

-- Not exact in general when R is not a domain:
R = kk[a]/ideal(a^3)
M = a^2*id_(R^3)
C = cramer(M,1);
Cr=chainComplex(C,M)
0==homology(1,Cr)
prune homology(1,Cr)