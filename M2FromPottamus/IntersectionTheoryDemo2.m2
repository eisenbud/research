getPackage "SimpleDoc"
getPackage "Schubert2"
path
restart

loadPackage "Schubert2"
viewHelp Schubert2

grassmannian = (m,n) -> flagBundle({m+1, n-m})

--number of lines on a general hyp of degree 2n-3 in Pn
time for n from 3 to 10 do(
     G=grassmannian(1,n);
     (S,Q) = G.Bundles;
     d = 2*n-3;
     print integral chern symmetricPower(d, dual S))

--degree and genus of the curve of lines on a general hyperplane of degree 2n-4 in Pn
for n from 3 to 10 do(
     G=grassmannian(1,n);
     (S,Q) = G.Bundles;
     T = G.TangentBundle;
     d = 2*n-4;
     N = symmetricPower(d, dual S);
     h = chern_1 Q;
     deg =integral(h* chern_(rank N) N);
     gen=(2-integral((chern_(rank N) N)*(chern_1 T - chern_1 N)))/2;
     print(deg,gen)
)          

--degree and genus of a complet intersection in Pn, same method
n=3, deglist = {2,3} -- canonical curve in P3
curve = (n,deglist)->(    
     G=flagBundle({1,n}, VariableNames=>{s,q}); -- projective space
     (S,Q) = G.Bundles;
     h = chern_1 Q;
     T = G.TangentBundle;
     D = dim G;
     d = D-1;
     N = abstractSheaf(G,ChernClass =>product(degs, i->(1+i*h)), Rank=>d);
     deg =integral(h* chern_(rank N) N);
     integral((chern_(rank N) N)*(chern_1 T - chern_1 N));
     gen=(2-integral((chern_(rank N) N)*(chern_1 T - chern_1 N)))/2;
     <<"(degree, genus) ="<< (deg,gen)<<endl)
curve(3,{2,3})

--first and top Chern classes of the universal fano scheme for a Pm of degree d hypersurfaces in Pn
n=3
m=5
d=4
P = flagBundle({1,m}, VariableNames=>{z,q1})
(Z,Q1)=P.Bundles
V = abstractSheaf(P,Rank =>n+1)
G = flagBundle({2,n-1},V,VariableNames=>{s,q})
(S,Q) = G.Bundles
p = G.StructureMap
ZG = p^*(dual Z)
chern_(d+1)(ZG**symmetricPower_d dual S)
chern_1(ZG**symmetricPower_d dual S)

--first and top chern classe of the tangent bundle of grass of lines in Pn are simple
for n from 4 to 8 do(
     for k from 1 to (n+1)//2 do(
G = grassmannian(k,n);
(S,Q) = G.Bundles;
h = chern_1 Q;
D = dim G;
--two simple relations
print ((n+1)*h ==chern_1 G.TangentBundle);
print (integral chern_D G.TangentBundle == binomial(n+1, k+1));
--but the next one's mysterious:
print(k,n, chern_2 G.TangentBundle);
))



G = grassmannian(3,7)
(S,Q) = G.Bundles;
h = chern_1 Q
D = dim G
print(integral chern_D G.TangentBundle == binomial(8, 4))

h^(D-1)*(chern_1 G.TangentBundle)
     

--the curve of lines on a quartic 3-fold:
G = flagBundle({2,3},VariableNames =>{s,t})
(S,Q) = G.Bundles
T = G.TangentBundle
N = symmetricPower(4,dual S)
g=(2-integral((chern(1,T)-chern(1,N))*chern(5, N)))//2
deg = integral((chern_5 N)*(chern_1 Q))

restart
n=3;
d=3;
S=kk[x_0..x_n]
f = sum(0..min(n,(d-1)//2), i->x_(i+2)*x_0^(2*i)*x_1^(d-1-2*i))

ideal singularLocus ideal f
transpose jacobian ideal f

--Chern classes of the bundle of principal parts on projective space
restart
needsPackage "Schubert2"
Pparts = (n,m) -> (
      projectiveSpace(n,base(d),VariableName => H);
      product(m+1, i->(1+(d-i)*H)^((-1)^i*binomial(n+i,n)))
      )
for i from 0 to 5 do print Pparts(2, i)

--
n=2
X = base(n,Bundle=>(Om,n,c), Bundle=>(lambda,1,d))
intersectionRing X
--why isn't the intersection ring truncated at the dimension??
product(2, i-> (chern (lambda**symmetricPower(i,Om)))^((-1)^i))
use X
X.IntersectionRing = QQ[d]/(d^2)
1/(1-d)
