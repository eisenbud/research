------------------
--same with 6 gens
restart
S=kk[x_1..x_6,y_1..y_15]
sk= genericSkewMatrix(S,y_1,6)
X=(vars S)_{0..5}
m=X*sk
F=res(coker m)
betti F
f=F.dd_2*random(source F.dd_2,S^{5:-4 })
codim (minors(1,f)+ideal X)
R=S/ideal X
ev=map(R,S)
ev f