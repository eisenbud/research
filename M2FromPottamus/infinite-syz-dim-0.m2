restart
kk=ZZ/101
S = kk[x,y_1..y_2,z_1..z_2]
i=x*ideal(y_1..y_2) + ideal(z_1*x -y_1^2,
                            z_2*x -y_2^2, 
			    x*z_1^2, 
			    x*z_2^2, 
			    y_1^5, 
			    y_2^5)

R=S/i
m1 = matrix"x"
m2 = matrix{{y_1},{y_2}}
prune homology(1, chainComplex(m2, m1))
ann coker m1
ann ideal x

