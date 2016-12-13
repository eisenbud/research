restart
--test the relation between the regularity of a monomial ideal
--and the regularity of the image under the rational map it defines.

--regularity of an ideal

--code for random ideals:
randomMonomial = (d,S)->(
     m := basis(d,S);
     m_(0,random rank source m))

randomMonomialIdeal=(L,S)->(
     --L=list of degrees of the generators
     ideal apply(L, d -> randomMonomial(d,S))
     )

randomBinomialIdeal=(L,S)->(
     --L=list of degrees of the generators
     ideal apply(L, d->randomMonomial(d,S)-randomMonomial(d,S))
     )

regSeq=(L,S)->(
     --forms an ideal generated by powers of the variables.
     --L=list of NN. uses the initial subsequence of L as degrees of variables
     ideal for m to min(#L,rank source vars S)-1 list S_m^(L_m))

-----
regi = i-> regularity module i

----------
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

S=kk[a,b,c]
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

testr=(d,m)->test (i= trim ((ideal vars S)*regSeq(toList(3:d-1),S)+
	  randomMonomialIdeal(toList(m:d),S)))


scan(20, sss->testr(3+ (random 4),random 5))