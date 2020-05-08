--build the determinantal ideals of r\times r matrices
--coming from multiplication in the symmetric algebra:
--Sym^p(k^n) \otimes Sym^q(k^n) \to Sym^(p+q)(k^n).

--Note: p=1, 2x2 minors, gives the veronese embedding of P^{n-1} by |O(q+1)|
--Also, the maximal minors have the codim of the generic case, it seems (1-generic).

productMatrix = method(Options => {Kind => "Symmetric"})
productMatrix(ZZ,ZZ,ZZ) := opts -> (n,p,q) ->(
kk := ZZ/101;
T := null;
if opts.Kind == "Skew" 
 then
T = kk[X_0..X_(n-1), SkewCommutative => true] 
 else
T = kk[X_0..X_(n-1)];
makeScalars := map(kk,T,toList(numgens T:0));
ro := flatten entries basis(p,T); 
co := flatten entries basis(q,T);
B := basis(p+q,T);
--Svars := flatten entries B;
--S := kk[x_0..x_(#Svars-1)];
S := kk[x_0..x_(numcols B-1)];
--M := map(S^(#ro), S^{#co:-1}, (i,j) -> (
--        if ro_i*co_j == 0 then 0_S else
--	S_(position(Svars, m -> m==ro_i*co_j))))
map(S^(#ro), S^{#co:-1}, (i,j) -> (
        if ro_i*co_j == 0 then 0_S else(
	   v := B//(ro_i**co_j);
	   ((makeScalars v)*transpose vars S))_(0,0)))
   )

end --
restart
needsPackage"PieriMaps"
viewHelp PieriMaps
load "determinantalIdeals.m2"
viewHelp pieri


(n,p,q,r) = (7,2,2,2)
productMatrix(n,p,q)
M=productMatrix(n,p,q, Kind=>"Skew")
load "determinantalIdeals.m2"
n = 2, p = 4,q=4, r=4
M = productMatrix(n,p,q)
I = minors(r,M);
c = codim I
R = kk[x_1..x_c]
minimalBetti I    
minimalBetti coker basis(r,R)
--we seem to be getting a deformation of the forms of degree r
--in codim many variables (codim == p+q)

restart
load "determinantalIdeals.m2"
--n = 3, p=2,q=2, r=5 -- this has the generic height for a symmetric matrix
--n = 3, p=2,q=2, r=4-- this has the generic height for a symmetric matrix
-*n = 3, p=2,q=2, r=3 -- codim 9, not the generic codim for symm matrix, but CM with betti table
o7 = total: 1 148 840 2187 3300 3060 1701 490 46 3
         0: 1   .   .    .    .    .    .   .  . .
         1: .   .   .    .    .    .    .   .  . .
         2: . 148 840 2187 3300 3060 1701 490 36 .
         3: .   .   .    .    .    .    .   .  . .
         4: .   .   .    .    .    .    .   . 10 3
*-
--n = 3, p=2,q=2, r=2 -- the veronese
M = productMatrix(n,p,q)
I = minors(r,M);
c = codim I
degree I
R = kk[x_1..x_c]
B = minimalBetti I
c == pdim B
minimalBetti coker basis(r,R)

-------------
-----Skew cases

restart
load "determinantalIdeals.m2"
n = 16, p=2,q=2, r=2 -- generic skew
M = productMatrix(n,p,q, Kind =>"Skew");
I = minors(r,M);
c = codim I
degree I
B = minimalBetti I
c == pdim B
--CM:
--(n,1,1,r)
--(5,1,2,2), (5,1,2,3)
--((5,2,2): all are CM

--Not CM
--(5,1,2,4), (5,1,2,5)
--CM






