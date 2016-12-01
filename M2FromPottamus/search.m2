kk=ZZ/5
S=kk[a,b,c]
test1=()->(
socle=random(S^1, S^{-27,-30});
i=ideal fromDual socle;
print betti mingens i;
--betti i^2;
--i2g=forceGB gens i^2;
random(S^1, S^{-36}) % gb i^2)
--print rank source mingens i^2)
time test1()
betti res i
betti mingens i^2

i2g=forceGB gens  i^2;

random(S^1, S^{-16}) % gb i^2

betti i2g
betti i^2

j=i;
betti mingens j
betti gens gb i^2

restart

for d from 5 to 20 do 
     for a from 1 to 25 do
     for b from 1 to 25 do
     for c from 1 to 25 do
     (if binomial(d+1,2) == binomial(a+3,2)+binomial(b+3,2)+2*binomial(c+3,2) then
	       print(d,a,b,c,c))


