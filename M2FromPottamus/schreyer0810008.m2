 

orderedSubsets= (P,k)->(
     L1:=subsets(P,k);
     select(L1, t-> t== sort t))

orderedPairs = P->(
L1=flatten apply(P, i->(apply(P, j-> (i,j))));
select(L1, t-> t_0<t_1))

orderedTriples = P->(
L1=flatten flatten apply(P, i->(apply(P, j-> apply(P,k->(i,j,k))))
);
select(L1, t-> t_0<t_1 and t_1<t_2))

///
P=toList(0..5)
orderedTriples P
orderedSubsets(P,4)
///

end
restart
load "schreyer081008.m2"

kk=QQ
n=5
W=apply(orderedPairs toList(0..n), t->t_1-t_0)

S=kk[apply(orderedPairs toList(0..n), t->x_t), Weights=>W]
linearRelations = ideal apply(orderedTriples toList(0..n), t->(x_(t_0,t_2)-x_(t_0,t_1)-x_(t_1,t_2)))
R=S/linearRelations

lastrows=matrix(apply(n, i1->(i=n-i1;
Q=subsets(toList(1..i),i-1);
  shortrow=apply(Q, t->product(orderedPairs t,p->x_p));
  row=join(toList(n-i:0), shortrow))))

firstrow = matrix{apply(select(subsets(toList(0..n),n), 
	       i-> i=!=toList(1..n)),t-> product(orderedPairs t,p->x_p))}
M=transpose(firstrow || lastrows)
N=syz M;
N_0_0
E = entries N;

n=5
use S
mon = E_3_0
degree ideal mon
use S
degrees vars S
degree ideal mon
time select(L=apply(orderedSubsets (orderedPairs toList(0..n),degree ideal mon ), t->product(t, p-> x_p)),
     nom-> substitute(nom, R)== -mon)
substitute(L_0, R)

apply(decompose(ideal(E_1_0)), c->degree c)
apply (E, i-> flatten entries(coefficients i_0)_1)
apply (E, i->apply(decompose(ideal(i_0)), c->degree c) )


firstrow = n->(
Q=subsets(toList(1..i),i-1);
  shortrow=apply(Q, t->product(orderedPairs t,p->x_p));
  row=join(toList(n-i:0), shortrow))


sublists(toList(0..n),2)
viewHelp sublists
m=map(S^{0..n-1},S^(n+1), (i,j)->d_j^i)
m1 = m_{1..n}^{0..n-2}

isHomogeneous m
det m_{1,2,3}^{0,1,2}
j=2
det m_{}^{}
M=matrix(apply(n, i->(apply(n, j->(
			 mi
			 nj:=delete(j, toList(0..n));
			 det m1_nj
			 
			 