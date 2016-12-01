S=kk[a,x, Degrees=>{{1,1,0},{1,0,1}}]
i=ideal (a*x)
F=res i
F_0
F_1
(degrees (F_1))_0

restart
S=kk[a,b]
i=(ideal(vars S))^3
j=symmetricKernel(ideal(0_S), gens i)
T=kk[a,b,x_1..x_4,Degrees=>flatten {toList (2:{1,1}), toList (4:{1,0}) }]
g=map(T,ring j, matrix{{vars T}})
jj=g j
F=res jj
degrees (F_3)
degrees F_2
degrees F_1
degrees F_2