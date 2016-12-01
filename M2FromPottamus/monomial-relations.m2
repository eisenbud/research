regi = i-> regularity module i

--test the relation between the regularity of a monomial ideal
--and the regularity of the image under the rational map it defines.
test = i ->(
     reg1:=regi i;
     d:=(degree(i_0))_0;
     n:=rank source vars ring i -1;
     --n= dim of proj space
     T:=kk[Z_0..Z_(numgens i-1)];
     F:=map(S,T,gens i);
     I:=kernel F;
     reg2=regularity coker gens I;
     if reg1-d+n<reg2 then print toString i;
     use ring i;
print (reg1, reg1-d+n, reg2, reg1-d+n>=reg2))

load "randomIdeal.m2"
end

restart
load "monomial-relations.m2"
--test the relation between the regularity reg1 of a monomial ideal
--and the regularity of the image under the rational map it defines.
--In particular
S=kk[a,b,c]
i=ideal (a^6, a^5*b, b^6, c^6, a^2*b^2*c^2)
i=ideal vars S
test i
j=ideal (a*b*c^3 , b^3*c^2 , a^3*b*c, a^5)
test j -- FALSE! Not a morphism, not birational
d=5
m=3
test (i= trim (regSeq(toList(3:d),S)+randomMonomialIdeal(toList(m:d),S)))

--counterexample (by 1). Not birational
i=ideal(c^5,a^2*c^3,a^3*b*c,b^5,a*b^4,a^5)
test i

--A birational counterexample (by 2)
i=ideal(c^6,a^3*b*c^2,b^5*c,b^6,a*b^5,a^4*b^2)
test i
betti i
betti res i

--To make a birational example, try throwing in (vars S)*m for some
--monomial m of one lower degree:
testr=(d,m)->test (i= trim (--regSeq(toList(3:d),S)+
	  (ideal vars S)*randomMonomialIdeal(toList(1:d-1),S)+
	  randomMonomialIdeal(toList(m:d),S)))

--How about birational morphisms?
testr=(d,m)->test (i= trim (regSeq(toList(3:d),S)+
	  (ideal vars S)*randomMonomialIdeal(toList(1:d-1),S)+
	  randomMonomialIdeal(toList(m:d),S)))

scan(20, s->testr(2+random 8,random 5))
--counterexamples that are birational morphisms. But it's close, 
--and they are rare.
i=ideal(c^8,b^2*c^6,b^3*c^5,a*b^2*c^5,a^5*c^3,a^5*b^2*c,b^8,a^3*b^5,a^8)
i=ideal(c^9,a*c^8,a^2*b^6*c,a^7*b*c,b^9,a*b^8,a^2*b^7,a^3*b^6,a^9)
test i
betti res i

--How about embeddings?
testr=(d,m)->test (i= trim ((ideal vars S)*regSeq(toList(3:d-1),S)+
	  randomMonomialIdeal(toList(m:d),S)))

scan(20, sss->testr(2+random 8,random 5))



print 
S=kk[a,b]
i=(ideal vars S)
test i^3
d=5
m=3
test (i= trim (ideal(a^d)+randomMonomialIdeal(toList(m:d),S)))


     
