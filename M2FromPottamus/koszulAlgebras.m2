--functions to compute the hilbert function and its relation to 
--1-dependent processes.

probabilities = (i,n) ->(
     --produces the "probabilities" of j ones in a row, for j = 1..n,
     --coming from the Hilbert function of (ring i)/i, as if this
     --were a 1-dependent process.
     ss := (coefficients hilbertSeries(i, Order=>n+4))_1;
     H := flatten entries ss;
     H = apply(H, s -> lift(s,ZZ));
     H = apply(H, s -> promote(s,QQ));
     if #H<n+2 then H = H | toList(n+2-#H:0_QQ);
     print for m from 2 to n+1 list H_m;
     apply(toList(2..n+1), m -> H_m/((H_1)^(m))))

binaryDigits = n -> (
     --returns the list of  digits of the number n, written in binary
     r:=0;
     reverse while n>0 list (
	  r = n%2;
	  n = n//2;
	  r))
testMatrix = method()
testMatrix(List, List)  := (b,p)->(
     --p is a list of the probabilities of getting i 1's in a row
     --b is a list of 0's and 1's.
     --This routine produces the matrix whose determinant is the
     --probability of the given pattern b.
     z1 := (positions(b,b->b===0))/(m->m+1);
     zeros := {0}|z1|{1+#b};
     m = #zeros-1;
     P := {1,1}|p;
     map(QQ^m, QQ^m, (i,j) -> (
	       if i > j+ 1 then 0
	       else P_(zeros_(j+1) - zeros_i)))
     )
testMatrix(List) := p -> testMatrix(toList(#p:0),p)

testIdeal = (i,m)->(
     --returns a hash table whose keys are all the 0,1 patterns
     --with m bits, and whose values are the probabilities of
     --computed as if the Hilbert function of (ring i)/i determined
     --a 1-dependent process (which it does iff all the values, for all m,
     --are non-negative.)
     p := probabilities(i,m+1);
     D := new MutableHashTable;
     scan(0..2^m-1, t ->(
	  b = binaryDigits t;
	  B = toList(m-#b:0)|b;
	  D#B = det testMatrix(B,p)));
     new HashTable from D)

reportNegatives = H ->(
     --prints the pairs in the Hash table H such that
     --the value is negative.
     scanKeys(H, i-> if H#i<0 then print(i,H#i)))     

probFromGraph = method()
probFromGraph(Matrix,List, ZZ) := (L,noLoops,d) ->(
     -- L is an m x 2 matrix, viewed as a list of directed edges given by the rows, which are integers.
     --noLoops is a list of those vertices that do NOT have loops attached.
     --the program makes the square matrix (including the diagonal entries 
     --that are not on the list noLoops) and 
     --constructs from it the sequence of probabilities of j heads, j=1..d. If there are n vertices,
     --this is the sum of the entries of the k-th power of the matrix divided by n^k.
n := numrows L;
M := mutableMatrix map(QQ^n, QQ^n,0);
L1 := entries L; 
scan(L1, i->M_(i_0,i_1) = 1_QQ);
m := matrix M;
--I :=id_(QQ^n);
I = map(QQ^n, QQ^n, (i,j)-> if i!=j or member(i, noLoops) then 0_QQ else 1_QQ);
row := map(QQ^1, QQ^n, matrix {toList( n:1_QQ)});
col := transpose row;
m = m+I;
mm := m;
p:=m;
P := for i from 1 to d list (
     p = row*mm*col; --print p;
     mm = m*mm;  
--     print p_(0,0);print d;
     p_(0,0)
     );
print P;
for i from 1 to d list P_(i-1)/(n^i)
)

probFromGraph(Matrix, ZZ) := (L,d) -> probFromGraph(L,{},d)

probFromGraph(List,List,ZZ) := (LL, noLoops, d) -> probFromGraph(cycleMatrix LL, noLoops,d)
probFromGraph(List,ZZ) := (LL,  d) -> probFromGraph(cycleMatrix LL,d)
     --Here the graph is a single loop, and LL is a list of +/- 1's 
     --specifying the orientations of the edges, in order;
     --thus LL = {1,1,1} is the oriented triangle and LL = {1,1,-1} is one of the non-oriented triangles.

cycleMatrix = LL ->(
     --takes a list LL of n numbers
     --and returns a matrix with two columns, with entries in the i-th  row
     --i,i+1 if LL_i = 1 and i+1,i otherwise. (matrix elements are taken mod n)
     n := #LL;
     map(ZZ^n, ZZ^2, (i,j) -> (
	       if j == 0 then (if  LL_i == 1 then i%n else (i+1)%n)
	       else if j == 1 and LL_i == 1 then (i+1)%n else i%n)
	  )
     )
///
restart
load "koszulAlgebras.m2"
cycleMatrix{1,1,1}
cycleMatrix{1,1,0}

///

isTotallyNonNegative = M ->(
     --returns true if M is a totally non-negative matrix, else false.
     nrows := numrows M;
     ncols := numcols M;     
     for i from 0 to nrows-1 do(
	  for j from 0 to ncols-1 do (
	       if i>j and det M_{i-j..i}^{0..j} < 0 then return false;
	       if i<=j and det M_{0..i}^{j-i..j}<0 then return  false);
	  );
     true)

--	       if i>j then print M_{i-j..i}^{0..j};
--	       if i<=j then print M_{0..i}^{j-i..j}
		    
		    
/// Tests:
restart
load "koszulAlgebras.m2"

N=map(ZZ^3,ZZ^3, (i,j) ->2+i-j)
isTotallyNonNegative N

L = matrix"0,1;1,2;2,3;3,0"

P=probFromGraph(L, 10)


P=probFromGraph({1,1,1,1}, 10)

L = matrix"0,1;2,1;2,3;0,3"
P=probFromGraph(L, 10)
P=probFromGraph(L,{0,1,2,3}, 10)



S = ZZ/101[a..d]
i = ideal"ac,bd"
probabilities(i,10)
j = ideal"ac,bd,a2,b2,c2,d2"
probabilities(j,10)
///

end
restart
load "koszulAlgebras.m2"
kk=ZZ/101
S = kk[a,b,c,d]
i = ideal(a^2)
j = ideal(a^3)
p = probabilities (i,5)
testMatrix p
det testMatrix({0,0,0},p)
time D = testIdeal(i,10)
pairs D
reportNegatives D
hilbertSeries i

--the directed graphs on a cycle of 5 verts
restart
load "koszulAlgebras.m2"
L1 = {1,1,1,1,1}
L2 = {1,1,1,1,0}
L3 = {1,1,1,0,0}
L4 = {1,1,0,0,0}
L5 = {1,1,0,1,0}
S = ZZ/101[a..e]
i=ideal"ac,ad, bd,be, ce"
betti res i
probabilities(i,10)
probFromGraph(L1,10)
probFromGraph(L2,10)
probFromGraph(L3,10)
probFromGraph(L4,10)
probFromGraph(L5,10)
