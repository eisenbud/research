diffs = F-> diff(vars ring F, F)
HK = i -> prune homology (koszul(i, diffs F),koszul(i+1, diffs F))

kk=ZZ/32003
n=4

betti res HK 0
betti res HK 1
betti res HK 2

showme =  n->(
     S=kk[x_1..x_n];
     F=product(1..n, i->x_i);
     scan (n-1, i->print betti res HK i)
     )

showme 6
