S=kk[a,b,c,d]
i=ideal(a^2+b*c,c^2)
m=gens i

quadricsToMatrix= m->(
n=rank source m
x=symbol x;
T=kk[x_1..x_n];
ST=S**T;
mm=substitute (m, ST);
xx=substitute(vars T, ST);
aa=substitute(vars S, ST);
contract(aa,transpose contract(aa,Q))

contract(aa,Q)
aa
Q

quadricsToMatrix m
