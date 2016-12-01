--Do k+1 quadrics through a point in $k+1$ vars have to have a lin syz?
k=2
d=3
S = kk[x_0..x_k]
i = ideal( (matrix{{x_1..x_k}})*random(S^{k:-1}, S^{k+1:-d}))
betti res i
