S = QQ[x,y]
f = x^2+y^2-2
psi = x-y^2
phi =  x-1
matrix{{f}} // matrix{{phi,psi}}
f == (x+2)*phi-psi

R = det sylvesterMatrix(psi,phi,y)
lambda = x-1
R == lambda*phi + (0*psi)
(lambda*f) 
quotientRemainder(lambda*f, psi)
lambda*f == x*y*psi + (-x^2*y+x^2)

----


