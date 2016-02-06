

S=ZZ/101[x_(1,1)..x_(3,3)]

U=matrix {{0, 0, x_(1,1), x_(1,2), x_(1,3), 0}, {0, 0, -x_(2,1), -x_(2,2), x_(2,3), x_(3,3)}, {-x_(1,1),
       x_(2,1), 0, 0, x_(2,1), -x_(3,1)}, {-x_(1,2), x_(2,2), 0, 0, -x_(2,2), x_(3,2)}, {-x_(1,3), -x_(2,3),
       -x_(2,1), x_(2,2), 0, 0}, {0, -x_(3,3), x_(3,1), -x_(3,2), 0, 0}}
X=map(S^3,,transpose genericMatrix(S,x_(1,1),3,3))

perm3=(pfaffians(6,U))_0
det3=det X
perm3+det3
perm3-det3
U
det(U_{1..4}^{1..4})

dU=decompose pfaffians(4,U)
tally apply(dU,c->(codim c, degree c))
singP=decompose ideal jacobian ideal perm3
tally apply(singP,c->(codim c,degree c)) 

