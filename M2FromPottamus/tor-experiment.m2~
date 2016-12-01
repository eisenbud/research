--In this example the annihilator of Tor is computed wrong
--(or not at all) both in v52 and v58
restart
S=kk[x_0..x_4]
R=S/(ideal(x_0,x_1)*ideal(x_2,x_3))
J=ideal vars R

M=R^1/J
d=3
N=(R^1)/(J^d)
annihilator Tor_1(M,N)
annihilator Tor_1(N,M)
--the two are different!! The second is correct...
--should be the annihilator of M, which is
--(x_0,...,x_4)

restart
S=kk[x_0..x_3]
R=S/ideal(x_0*x_1-x_2*x_3)
J=ideal vars R

M=R^1/J
d=3
N=(R^1)/(J^d)
Tor_1(M,N)
annihilator Tor_1(M,N)
-- gives error msg "stdio:8:1: monomial overflow" 

