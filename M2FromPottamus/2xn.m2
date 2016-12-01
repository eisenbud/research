--Programs for constructing all the types of 2xn matrices of linear forms

--RNC blocks
--Specify ring S, first var number m, size d:
rnc=(S,m,d)-> map(S^2,S^d,(i,j)->S_(m+i+j))

--Jordan blocks
--Specify ring S, first var number m, size d, eigenvalue lambda
jordan=(S,m,d,lambda)-> map(S^2,S^d,
     (i,j)->if i == 0 then lambda*S_(m+i+j) else 
               (if j==0 then 0_S else S_(m+i+j-2))
		    )
--Nilpotent blocks
--Specify ring S, first var number m, size d:
nilp=(S,m,d)-> map(S^2,S^d,
     (i,j)->if i==0 then (if j<d-1 then S_(m+i+j) else 0) else
                    (if j==0 then 0_S else S_(m+i+j-2))
		    )
--
--Put together groups of blocks of same type.
--Specify ring S, first var number, size d:

rncs=(S,m,L)->(
     count:=m;
     matrix{apply(L, i->(count=count+i+1;
     rnc(S,count-i-1,i)))}
     )

scroll=(S,m,L)->(
     count:=m;
     matrix{apply(L, i->(count=count+i+1;
     rnc(S,count-i-1,i)))}
     )

nilps=(S,m,L)->(
     count:=m;
     matrix{apply(L, i->(count=count+i-1;
     nilp(S,count-i+1,i)))}
     )

jordans=(S,m,M)->(
     count:=m;
     matrix{apply(M, i->(count=count+i_0+1;
     jordan(S,count-i_0-1,i_0,i_1)))}
     )

----
--PUt it all together
matrixPencil=(S,m,Lscroll,Lnilp,Ljordan)->(
     matrix{{rncs(S,m,Lscroll),
	  nilps(S, m+#Lscroll+sum Lscroll , Lnilp),
	  jordans(S,m+#Lscroll+sum Lscroll+sum Lnilp-#Lnilp,Ljordan)}}
     )

--Find the arithmetic degree of an ideal, using primary decomposition
arithmeticDegree= i->(
pd:=primaryDecomposition i;
pc= apply(pd, codim);
codims:=unique sort pc;
isolated=positions(pc, i->(i<=codims_0));
j=ideal(1_(ring i));
sum apply(codims, m->(
     j1=j;
     next = positions(pc, i->(i==m));
     j=intersect(j, intersect(pd_next));
     degree ((j1*S^1)/(j*S^1))
     ))
)

end

restart

--tests:
load "2xn.m2"
S=kk[vars(0..9)]     
rnc(S,2,4)
jordan(S,2,7,4)
nilp(S,2,4)
L={2,2,3}
scroll(S,0,L)
nilps(S,0,L)
betti res minors(2, nilps(S,0,{2,3,3}))
codim minors(2, nilps(S,0,{2,3,3}))
M={{2,3},{2,5},{3,7}}
jordans(S,0,M)

--
restart
load "2xn.m2"
S=kk[vars(0..9)]
Lscroll={2}
Lnilp={2,2}
Ljordan={{3,0}}

m=matrixPencil(S,0,Lscroll,Lnilp,Ljordan)
i=minors(2,m);
betti res i
codim i -- =4
degree i -- = 1
show (pd=primaryDecomposition i)
degree pd_0 -- =1
degree ((pd_0*S^1)/(intersect(pd_1,pd_0)*S^1)) -- =2
degree ((intersect(pd_1,pd_0)*S^1)/(intersect(pd_0,pd_1,pd_2)*S^1)) -- =2
--This example satisfies the "arithmetic smallness condition"
--arith deg <= codim +1 
--for plane sections of a 2-regular scheme. In this case it's an equality!?!

--Note: the codims of the ideals listed in a primary decomp are not always
--in ascending order!

arithmeticDegree i

intersect(ideal(a), pd)
help select

pc=apply(pd, codim)
min pc
positions(pc, i-> i>4)
help List
help sort
Ideal ? Ideal := (i,j)-> 
if (codim i) <= (codim j) then "<=" else 
(if (codim i) == (codim j) then "==" else ">")

