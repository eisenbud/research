--Test a "random" linearly presented ideal in 3 variables for the--validity of the annihilation conjecture.restartload "symmetricPowerModule.m2"load "randomIdeal.m2"linPres = I -> ideal mingens truncate(max flatten degrees source syz gens I -1, I)kk=ZZ/32003S=kk[x,y,z]D={2,3,5}L={3,3,3}i1=regSeq(D,S)i2=randomBinomialIdeal(L,S)i=linPres(i1+i2)betti res id=max flatten degrees source gens isymmetricPowerModule(2*d+1, module i)