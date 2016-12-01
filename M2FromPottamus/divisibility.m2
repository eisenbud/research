kk=QQ
S=kk[t]
f=(k,d,t)->(product(k,i->t+i*d)/(k!))
3!
f(3,2,t)
apply(8, i->f(3,5,i))
apply(8, i->f(2,3,i))
