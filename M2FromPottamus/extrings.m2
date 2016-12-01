A = QQ[x,y]
B = A/(x^2,y^2)

tallMod = method()
tallMod(ZZ) := n -> (
     coker map(B^(n+1), n, (i,j) -> (
	       if i == j then x
	       else if i == j+1 then y
	       else 0))
     )
shortMod = method()
shortMod(ZZ) := n -> (
     coker map(B^n, n+1, (i,j) -> (
	       if i == j then x
	       else if j == i+1 then y
	       else 0))
     )
shortMod 2
tallMod 2

M = tallMod 2

columns = method()
columns(Nothing) := N -> {}
columns(Matrix) := A -> (
     if A == 0 then {}
     else apply(numgens source A, i -> submatrix(A, {i}))
     )
niceBasis = method()
niceBasis(Matrix, Matrix) := (f, A) -> (
     v := fold(columns f, (p,q) -> p || q);
     map(target A, 1, (i,j) -> v_0_i) // A
     )
ExtTable = method()
ExtTable(ZZ,ZZ,Module) := (i,j,M) -> (
     if not isCommutative ring M then error "'ExtTable' not implemented for noncommutative rings.";
     if i >= 0 and j >= 0 then (
	  C := resolution(M,LengthLimit=>i+j+2);
	  b := C.dd;
	  complete b;
	  P := trim homology(Hom(b_(i+1),M), Hom(b_i,M));
	  Q := trim homology(Hom(b_(j+1),M), Hom(b_j,M));
	  R := trim homology(Hom(b_(i+j+1), M), Hom(b_(i+j), M));
	  print "table:";
	  print(j, Q, Ext^j(M,M));
	  print(i, P, Ext^i(M,M));
	  print(i+j, R, Ext^(i+j)(M,M));
	  apply(columns mingens P,
	       v -> (
		    G := res(coker b_(i+1), LengthLimit => j+1);
		    f := map(C_0, G_0, (m,n) -> v_0_(m+n*numgens M));
		    p := (extend(C, G, f))_j;
		    apply(columns mingens Q,
			 w -> (
			      g := map(C_0, C_j, (m,n) -> w_0_(m+n*numgens M));
			      print(niceBasis(g, mingens Q), 
				   niceBasis(f, mingens P), 
				   niceBasis(g*p, mingens R));))));
	  )
     )

Ext(M,M)
ExtTable(0,1,M)
ExtTable(1,1,M)
(res M).dd
ExtTable(2,1,M)

N = shortMod 2
Ext(N,N)
ExtTable(0,1,N)
ExtTable(1,1,N)
ExtTable(2,1,N)

M = tallMod 3
Ext(M,M)
ExtTable(1,1,M)
ExtTable(2,1,M)
(res M).dd
ExtTable(3,1,M)

jordanMod = method()
jordanMod(ZZ) := n -> (
     coker map(B^n, n, (i,j) -> (
	       if i == j then x
	       else if j == i+1 then y
	       else 0))
     )

J = jordanMod 3

Ext(J,J)
ExtTable(1,1,J)
ExtTable(1,2,J)

d=5
degree Ext^2(tallMod(d), tallMod(d))

