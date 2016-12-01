kk=ZZ/32003
R=kk[x,y,s,t]
f1= matrix{{s*x^2, -x*y*(s+t), t*y^2}}
betti(FF= res coker f1)
FF.dd_2
FF.dd_3
f2=(f1|0)||(0|f1)
betti(FF= res coker f2)
FF.dd_2
FF.dd_3

decompose ideal f1
f1
f1= matrix{{s*x^2,s*x*y,t*y^2}}
betti(FF= res coker f1)
FF.dd_2
FF.dd_3
f2=(f1|0)||(0|f1)
betti(FF= res coker f2)
FF.dd_2
FF.dd_3
i=annihilator coker f2
decompose i


kk=ZZ/32003
R=kk[x,y,s,t]
f1= matrix{{s^2*x^2, -x*y*(t^2), s*t*y^2}}
betti(FF= res coker f1)
FF.dd_2
FF.dd_3
f2=(f1|0)||(0|f1)
betti(FF= res coker f2)
FF.dd_2
FF.dd_3

betti res intersect(ideal(a,b),ideal(c,d))

betti res( i= (ideal(a,b))^2+ideal(c^3*a+d^3*b))
top i
