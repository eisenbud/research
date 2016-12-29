multiQuadric = (S,L) ->(
    trailing = numgens S -sum L;
    if trailing<0 then error("too many specified");
    vars(S)* 
	(S**diagonalMatrix(
	    flatten apply(#L, i->toList(L_i:i))|apply(trailing, i-> random 100000)
	    ))*
	transpose vars S)

row2 = F ->(
apply(n-1,m->#select(degrees F_(n-m-1), d -> d =={n+1-m})))

testQuadPencil = (S,L) ->(
    n := numgens S;
    Q := matrix{{sum(n,i->S_i^2)}}| multiQuadric (S,L);
    I := ideal fromDual Q;
    drop(row2 res I,1))


end--
--watch out for small random numbers!
restart
load "quadraticPencils.m2"

n=10
S = ZZ/32003[x_0..x_(n-1)]

matrix apply(n,r-> testQuadPencil(S,{2}))
matrix apply(n,r-> testQuadPencil(S,{r}))
matrix apply(n-2,r-> testQuadPencil(S,{2,r}))

netList apply(n-5,r-> testQuadPencil(S,{3,r}))
netList apply(n-5,r-> testQuadPencil(S,{r}))
netList apply(n-5,r-> testQuadPencil(S,{3}))
L1 = {2,2};L2 = {4}
testQuadPencil(S,L1)+testQuadPencil(S,L2) ==testQuadPencil(S,L1|L2)


S = QQ[a,b,c,d]
Q1 = sum(numgens S,i->S_i^2)
Q2 = multiQuadric(S,{2})
Q2 = c^2+2*d^2

Q = matrix{{Q1,Q2}}
I = ideal fromDual Q;
F = res I
betti F
F.dd_4
