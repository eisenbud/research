restart
n=4
N=n*(n-1)
S=kk[t,x_1..x_n]
F=product (1..n, j->product(1..n,(i)->if i==j then 1_S else (t*x_i-x_j)))
E=(coefficients({0},F))_1
transpose E
E1=E_{0..(N//2-1)}
T=kk[z_1..z_(N//2)]
p=map(S,T,E1)
kernel p
