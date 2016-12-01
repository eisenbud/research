--- we consider a 4x2x2 tensor
restart
R=ZZ/101[x_{1,1,1}..x_{4,2,2}]
dim R
phiFlat=genericMatrix(R,4,4)
--- note that this equals the flattening of phi as in sec 12 of our paper

L=subsets(4,2)
K1=apply(L,i->( det submatrix(phiFlat,{0,2},i)))
M1=map(R^1,R^6,(i,j)->((K1)_j ))
K2=apply(L,i->( (det submatrix(phiFlat,{0,3},i) + 
	       det submatrix(phiFlat,{1,2},i)) ))          

M2=map(R^1,R^6,(i,j)->((K2)_j )) 

K3=apply(L,i->( det submatrix(phiFlat,{1,3},i)))         
M3=map(R^1,R^6,(i,j)->((K3)_j ))  
partial1=M1||M2||M3
p1=partial1
pL =map(target p1,source p1,(i,j)-> leadTerm partial1_(i,j))
betti res coker pL
codim ideal flatten entries pL
codim ideal flatten entries contract (transpose vars R,gens ideal flatten entries pL) 
pL
--- res coker partial1 equals F(\phi,w) where \phi is 4x2x2 and w=(0,0,2).
---  this is the example from section 12 of our paper.
--- note that coker partial1is CM of codimension 2. 
M=coker partial1;
betti res coker partial1

--- this is the fitting ideal
fitM=minors(3,partial1);
betti res fitM

--- here is the annihilator of M
annM=ann(M);
betti res annM
codim annM
--- this is not cohen-macaulay either, but it's better than the fitting ideal.
--- Barring a mistake, pdim(fitM)=8>pdim(annM)=2, but we want an ideal
--- with pdim=1.
E = prune Hom(M,M)
betti res E
codim E
