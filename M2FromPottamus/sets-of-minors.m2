restart
S=kk[vars(0..2*5)]
m=genericMatrix(S,2,5)
i=minors(2,m)
count=-1
for L in  subsets(9) do(
count=count+1;
j=ideal ((gens i)*map(source gens i, S^{#L:-2},i_L));
print (count, L, j==radical j)
)


restart
S=kk[vars(0..2*5)]
m=genericMatrix(S,2,5)
i=minors(2,m)
L=(subsets(9))_86
j=ideal ((gens i)*map(source gens i, S^{#L:-2},i_L));
j
radical j
