load "randomIdeal.m2"

freeRank = M ->(
--finds the free rank of a module
     T = ring M;
     f=syz transpose presentation M;
     specialize := map(kk,T,matrix{{numgens T:0_kk}});
     rank specialize f
     )

conormalRank = i->(
--finds the free rank if i/i^2
F:=res (i, LengthLimit =>2);
T:=(ring i)/i;
f:=substitute (transpose F.dd_2, T);
g:=syz f;
specialize := map(kk,T,matrix{{numgens T:0_kk}});
rank specialize g
)
g
f
--The following accepts a monomial ideal, and decides whether 
--one of the generators is s nonzerodivisor mod the others.
--it returns "true" if this is the case.
isTrivial = i->(
     val = false;
     supports = for t from 0 to (numgens i -1) list set support i_t;
     for t from 0 to (numgens i -1) do (
	  comp = set{};
	  for s from 0 to (numgens i-1) do (if s =!= t then comp = comp + supports_s);
          if not isSubset(supports_t, comp) then (
	       val = true; 
	       break));
     val
     )
end

restart
load "081102-Iyengar.m2"
kk=ZZ/101
S=kk[a,b,c,d]
i=ideal"ab,c2,cd, a2c+d3, b2d+ad2"
i1=ideal"ab,c2+ab,cd, a2c+d3, b2d+ad2"
f= presentation (module i1)
f**(S/i)

F=res (i, LengthLimit =>2);
T=(ring i)/i;
f=substitute (transpose F.dd_2, T);
f

--for m from 1 to 15 do(
--print freeRank ((S/i)**module(i^m))
--) -- every (i^n/i^(n+1) seems to have free rank 1.

print conormalRank i^2 -- zero! 

S=kk[a..e]
L=join(3:3,3:5,2:7)
time for m from 1 to 100000 do(
     i=trim randomMonomialIdeal(L, S);
     if not isTrivial i and conormalRank i > 0 then print toString i;
     )

S=kk[a,b,c]
i=ideal"ab,bc"
conormalRank i
presentation ((module i)/i^2)
