--various plane curve singularities, to 
--test normalization.

--Unibranch:
restart
load "IntegralClosure.m2"
kk=ZZ/32003
S=kk[a,b]
T=kk[t]
I=kernel map (T,S,{t^4, t^6+t^7})
integralClosure(S/I)
