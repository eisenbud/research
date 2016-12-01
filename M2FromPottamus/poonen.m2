S=kk[t,x,y,z]
f=(x+y^2)^2*y-z
f=(x+y^2)^2-z
f=(x+y)^2-z
f=(x^2+y^2-1)^2-z -- gives a gauss image that's smooth at the image of the plane!
f=(x^2+2*x+y^2)^2-z
F=homogenize(f,t)
J=singularLocus(S/F)
dim J
D=diff F
R=S/ideal(F)
project=map(R,S)
D1=map(R,S,project D)
G=ker D1
use S
m=matrix{{1_S,x,y,z}}
dehom =map(S,S,m)
dehom G
dim singularLocus G
presentation singularLocus G
