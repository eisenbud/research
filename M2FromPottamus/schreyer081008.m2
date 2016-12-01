--positivity in Boij-Soederberg decomp of a sheaf -- case of H^0.

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

lastrows=matrix(apply(n, i1->(i=n-i1;
Q=subsets(toList(1..i),i-1);
  shortrow=apply(Q, t->product(orderedPairs t,p->x_p));
  row=join(toList(n-i:0), shortrow))))

firstrow = matrix{apply(select(subsets(toList(0..n),n), 
	       i-> i=!=toList(1..n)),t-> product(orderedPairs t,p->x_p))}
M=transpose(firstrow || lastrows)


linearRelations = ideal apply(orderedTriples toList(0..n), t->(x_(t_0,t_2)-x_(t_0,t_1)-x_(t_1,t_2)))
R=S/linearRelations

N=syz substitute(M,R)
N_0_0
E = entries N;
Efac=apply(E, e-> (
	  mon = e_0;
	  use S;
     time select(L=apply(orderedSubsets (orderedPairs toList(0..n),degree ideal mon ), t->
	       product(t, p-> x_p)),
     nom-> substitute(nom, R)== -mon)))

K=matrix{{-1_S}}||matrix Efac_{1..#Efac-1}
MK=M*K
(flatten entries MK)/factor

use S

--decomposed kernel
time select(L=apply(orderedSubsets (orderedPairs toList(0..n),degree ideal mon ), t->product(t, p-> x_p)),
     nom-> substitute(nom, R)== -mon)


			 
			 