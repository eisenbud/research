newPackage(
	"K3Carpet",
    	Version => "0.1", 
    	Date => "November 17, 2016",
    	Authors => {{Name => "David Eisenbud", 
		  Email => "de@msri.org", 
		  HomePage => "http://www.msri.org/~de"}},
    	Headline => "K3 double structure on scrolls",
    	DebuggingMode => false
    	)

export {
    "carpet",
    "carpet1",
    "canonicalCarpet",
    "gorensteinDouble"}

-- Code here
carpet = method()
carpet(ZZ,ZZ) := (a1,a2) ->(
    kk := ZZ/32003;
    x := symbol x; y:=symbol y;
    a := min(a1,a2);
    b := max(a1,a2);
    S := kk[x_0..x_a, y_0..y_b];
    xmat := map(S^2, S^{a:-1}, (i,j) -> x_(i+j));
    ymat := map(S^2, S^{b:-1}, (i,j) -> y_(i+j));
    mat := xmat|ymat;
    if b==1 then return ideal ((det mat)^2)
    else if a ==1 then (
    	xmat = map(S^2,S^{2:-2},(i,j)->x_i*x_j);
	Iy := minors(2,ymat);
	Imixed := ideal apply(b-1,j->(det (xmat_{0}|ymat_{j+1})-det(xmat_{1}|ymat_{j})));
	return Iy+Imixed)
    else (
        Ix := minors(2,xmat);
    	Iy = minors(2,ymat);
	Imixed = ideal flatten apply(a-1, 
	    i-> apply(b-1,
		j->(det (xmat_{i}|ymat_{j+1})-det(xmat_{i+1}|ymat_{j}))
		)
	    );
	);
    Ix+Iy+Imixed)

--A different indexing, by genus and Clifford index (Cliff <= (g-1)//2))
canonicalCarpet = (gen,cliff) -> carpet(gen-cliff-1, cliff)

--Here's a structural approach that instead takes the kernel of the unique map of mainimal degree
--from the ideal of the scroll to the canonical module of the scroll. This code produces
--Gorenstein double structures on ACM varieties more generally. 
--computationally, the bare hands approach of carpet is much faster.

gorensteinDouble = I -> (
    --the script assumes that the "first" map I --> omega will be a surjection of the right degree
    c := codim I;
    F := res(I, LengthLimit => c);
    omega := coker transpose F.dd_c;
    ideal kernel (homomorphism (Hom(module I, omega))_{0})
    )
carpet1 = (a1,a2) ->(
    kk := ZZ/32003;
    x := symbol x; y:=symbol y;
    S := kk[x_0..x_a1, y_0..y_a2];
    xmat := map(S^2, S^{a1:-1}, (i,j) -> x_(i+j));
    ymat := map(S^2, S^{a2:-1}, (i,j) -> y_(i+j));
    mat := xmat|ymat;
    I := minors(2, mat);
    gorensteinDouble I
    )

beginDocumentation()

doc ///
Key
  K3Carpet
Headline
 The unique Gorenstein double structure on a surface scroll
Description

  Text
   There is a unique surjection from the ideal of a 2-dimensional rational normal scroll (other than the cone
   over a rational normal curve) onto the canonical module of the scroll (see *****), and the kernel
   of the this map is the ideal of a scheme that looks numerically like a K3 surface: a "K3 carpet".
   This package contains two routines for constructing this ideal: "carpet" uses a knowledge of the generators
   (see ****) while "carpet1" calls "gorensteinDouble", computing the ideal from first principles. The first
   is much more efficient. 
   
   The hyperplane section of a K3 carpet is a "canonical ribbon" indexing by genus and clifford index
   of the hyperplane is done in the routine "canonicalCarpet", which calls "carpet".
  Example
///

doc ///
   Key
    carpet
   Headline
    Ideal of the unique Gorenstein double structure on a 2-dimensional scroll
   Usage
    I = carpet(a1,a2)
   Inputs
    a1:ZZ
    a2:ZZ
   Outputs
    I:Ideal
   Consequences
    Item
     Creates the carpet over a new ring.
   Description
    Text
     Let X be a 2 x a1 matrix of indeterminates x_(i,j), and let Y be a 2 x a2 matrix of indeterminates y_(i,j).
     The "scroll ideals" are Ix, Iy, the ideals of 2 x 2 minors of X and Y. The ideal of the 2-dimensional
     rational normal scroll Scroll(a1,a2) is the ideal of 2 x 2 minors of X|Y.
     
     When a1, a2 > 1, the carpet ideal I is the sum Ix+Iy plus
     the ideal Imixed consisting of the quadrics "outside minor - inside minor", that is,
     det(X_{i},Y_{j+1})-det(X_{i+1}|Y_{j}),
     for each pair of (i,i+1), (j,j+1) in the ranges a1 and a2.
     when a1 = a2 = 1, I is the square of the det of X|Y
     when a1 = 1, a2>1, take the a2 minors and add the "outside-inside" ideal after replacing

     X = \begin{pmatrix}
     x_0\\
     x_1
     \end{pmatrix}
     
     by the 2 x 2 matrix
     
     \begin{pmatrix}
     x_0^2, x_0*x_1\\
     x_0*x_1, x_1^2
     \end{pmatrix}.
     
    Example
     betti res carpet(2,5)
   SeeAlso
    carpet1
    gorensteinDouble
    canonicalCarpet
///
 
TEST///
B11 = betti res carpet1(1,1)
B12 = betti res carpet1(1,2)
B21 = betti res carpet1(2,1)
B25 = betti res carpet1(2,5)
assert (B11 == betti res carpet(1,1))
assert (B12 == betti res carpet(1,2))
assert (B21 == betti res carpet(2,1))
assert (B25 == betti res carpet(2,5))
///

end--
restart
uninstallPackage "K3Carpet"
installPackage "K3Carpet"
check "K3Carpet"
viewHelp K3Carpet

for a1 from 1 to 5 do for a2 from a1 to 5 do 
     print (time carpet(a1,a2);, time carpet1(a1,a2);)

for g from 4 to 10 do for cliff from 2 to (g-1)//2 do time print betti res canonicalCarpet(g,cliff)



