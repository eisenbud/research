newPackage(
	"K3Carpets",
    	Version => "0.1", 
    	Date => "November 17, 2016",
    	Authors => {{Name => "David Eisenbud, Frank-Olaf Schreyer", 
		  Email => "de@msri.org", 
		  HomePage => "http://www.msri.org/~de"}},
    	Headline => "K3 double structure on scrolls",
    	DebuggingMode => true,
	PackageExports => {"CompleteIntersectionResolutions"}
    	)

export {
    "carpet",
    "carpet1",
    "canonicalCarpet",
    "gorensteinDouble",
    "homotopyRanks",
    "fixedSyzygyScheme",
    "canonicalHomotopies",
--    "nonMinRes",
--    "Characteristic",
    "FineGrading"}

carpet = method(Options =>{Characteristic => 32003,FineGrading=>false})
carpet(ZZ,ZZ) := opts -> (a1,a2) ->(
    if opts.Characteristic == 0 then kk := QQ else kk = ZZ/opts.Characteristic;
    x := symbol x; y:=symbol y;
    a := min(a1,a2);
    b := max(a1,a2);
    if opts.FineGrading == false then
    S := kk[x_0..x_a, y_0..y_b] else (
    degreeString := apply(a+1, i->{1,0,i,a-i})|apply(b+1, i->{0,1,i,b-i});
    S = kk[x_0..x_a, y_0..y_b, Degrees=>degreeString]);
    if opts.FineGrading == false then (
	xmat := map(S^2, S^{a:-1}, (i,j) -> x_(i+j));
        ymat := map(S^2, S^{b:-1}, (i,j) -> y_(i+j))
	)
    else(	
        xmat = map(S^{{0,0,0,0},{0,0,1,-1}}, S^(apply(a,j->{ -1,0,-j,-a+j})), (i,j) -> x_(i+j));
        ymat = map(S^{{0,0,0,0},{0,0,1,-1}}, S^(apply(b,j->{ 0,-1,-j,-b+j})), (i,j) -> y_(i+j))
	);
    mat := xmat|ymat;
    if b==1 then return ideal ((det mat)^2) -- in this case a == 1 as well
    else if a ==1 then (
	if opts.FineGrading == false then
    	xmat = map(S^2,S^{2:-2},(i,j)->x_i*x_j)
        else
        xmat = map(S^{{0,0,0,0},{0,0,1,-1}}, 
	           S^{{ -1,0,0,-2},{ -1,0,-1,-1}}, 
		   matrix{{x_0^2,x_0*x_1},{x_0*x_1,x_1^2}});
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
///
restart
loadPackage "K3Carpets"
I = carpet(1,3,FineGrading=>true)
I = carpet(1,3,FineGrading=>false)
betti (res I, Weights =>{1,1,0,0})
isHomogeneous I
degrees  S
isHomogeneous mat
degrees target mat
degrees source mat
mat
///

--A different indexing, by genus and Clifford index (Cliff <= (g-1)//2))
canonicalCarpet = method(Options=>{Characteristic=>32003,FineGrading => false})
canonicalCarpet(ZZ,ZZ) := opts -> (gen,cliff) -> 
     carpet(gen-cliff-1, cliff,Characteristic => opts.Characteristic, FineGrading => opts.FineGrading)

--Here's a structural approach that instead takes the kernel of the unique map of mainimal degree
--from the ideal of the scroll to the canonical module of the scroll. This code produces
--Gorenstein double structures on ACM varieties more generally. 
--computationally, the bare hands approach of carpet is much faster.
gorensteinDouble = method()
gorensteinDouble Ideal := I -> (
    --the script assumes that the "first" map I --> omega will be a surjection of the right degree
    c := codim I;
    F := res(I, LengthLimit => c);
    omega := coker transpose F.dd_c;
    ideal kernel (homomorphism (Hom(module I, omega))_{0})
    )

carpet1 = method(Options =>{Characteristic => 32003})
carpet1(ZZ,ZZ) := opts -> (a1,a2) ->(
    if opts.Characteristic == 0 then kk := QQ else
    kk = ZZ/opts.Characteristic;
    x := symbol x; y:=symbol y;
    S := kk[x_0..x_a1, y_0..y_a2];
    xmat := map(S^2, S^{a1:-1}, (i,j) -> x_(i+j));
    ymat := map(S^2, S^{a2:-1}, (i,j) -> y_(i+j));
    mat := xmat|ymat;
    I := minors(2, mat);
    gorensteinDouble I
    )

nonMinRes = method()
nonMinRes Matrix := m->(
F' := res image m;
complete F';
chainComplex apply(1+length F', j-> if j==0 then m else F'.dd_j)
)

fixedSyzygyScheme = method()
fixedSyzygyScheme(ChainComplex,ZZ,Matrix) := (C,i,v) -> (
           -- this is a fix for syzygyScheme, replacing 'resolution', (which replaces 
	   --the presentation of a cokernel
           -- by a minimal one) with nonMinRes, which resolves the image and then tacks on the 
	   --given matrix.  A better way to fix syzygyScheme would be to add an option to resolution.
	   --
	   --Note that the code in the system has "dual C[i]" in place of "dual C[-i]" in the first line,
	   --which seems to be wrong in a different way!
           g := extend(nonMinRes transpose (C.dd_i * v), dual C[-i], transpose v);
           minimalPresentation cokernel (C.dd_1  * transpose g_(i-1)))


canonicalHomotopies = method(Options=>{Characteristic=>32003,FineGrading=>false})
--note: returns the pair: the resolution F of the canonical Carpet
--and the function that used to be called h0 such that h0(i,j) is the j-th homotopy 
--with source F_j that corresponds
--to the i-th quadric.
canonicalHomotopies(ZZ,ZZ):= opts -> (g,cliff) -> (
    F := res canonicalCarpet(g,cliff, Characteristic => opts.Characteristic, FineGrading => opts.FineGrading);
    ff := F.dd_1;
    H := makeHomotopies1(ff,F);
    if opts.FineGrading == false then
    h0:= (i,j) -> submatrixByDegrees(H#{i,j},j+3,j+3)
    else
    h0 = (i,j) ->(
	
	dlist := select(flatten degrees H#{i,j}, de->de_0+de_1 == j+3);
	hashTable apply(dlist, de -> (de,submatrixByDegrees(H#{i,j},de, de)))
	);
    (F,h0)
    )
///
restart
loadPackage "K3Carpets"
(F,h0) = canonicalHomotopies(7,3, FineGrading=>true);
degrees F_1
h0(0,2)
degrees F_2
///
homotopyRanks = (g,cliff) ->(
(F,h0) := canonicalHomotopies(g,cliff);
print betti F;
ff := F.dd_1;
netList apply(numcols ff , i->{ff_i, apply(g-2, m->(rank h0(i,m+1)))})
)


beginDocumentation()

doc ///
Key
  K3Carpets
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
    (carpet, ZZ, ZZ)
    [carpet, Characteristic]
    [carpet, FineGrading]    
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
     Creates the carpet over a new ring. The characteristic is given by the option, defaulting to 32003.
     If the option FineGrading is set to true, then the ideal is returned with the natural ZZ^4 grading
     (the default is FineGrading => false).
   Description
    Text
     Let X be a 2 x a1 matrix of indeterminates x_{(i,j)}, 
     and let Y be a 2 x a2 matrix of indeterminates y_{(i,j)}.
     Let Ix, Iy be the ideals of 2 x 2 minors of X and Y. The ideal of the 2-dimensional
     rational normal scroll Scroll(a1,a2) is the ideal of 2 x 2 minors of X|Y.
     The ideal I to be constructed is the ideal of the unique (numerically) K3 scheme
     whose support is the scroll S(a1,a2).
     
     When a1, a2 > 1, the carpet ideal I is the sum Ix+Iy plus
     the ideal Imixed consisting of the quadrics "outside minor - inside minor", that is,
     det(X_{\{i\}},Y_{\{j+1\}})-det(X_{\{i+1\}}|Y_{\{j\}}),
     for each pair of (i,i+1), (j,j+1) in the ranges a1 and a2.
     
     When a1 = a2 = 1, I is the square of the det of X|Y.

     When a1 = 1, a2>1, I is defined as in the case a1,a2>1, for Imixed we
     replace

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
 
 doc ///
   Key
    canonicalCarpet
    (canonicalCarpet, ZZ, ZZ)
    [canonicalCarpet, Characteristic]
    [canonicalCarpet, FineGrading]    
   Headline
    Carpet of given genus and Clifford index
   Usage
    I = canonicalCarpet(g,cliff)
   Inputs
    g:ZZ
     desired genus
    cliff:ZZ
     desired clifford index
   Outputs
    I:Ideal
     ideal of the K3 Carpet of (sectional) genus g, Clifford index cliff
   Description
    Text
     This is just a re-indexing of the carpet script:
     canonicalCarpet(g,cliff) = carpet(g-cliff-1, cliff).
     Here the natural choices for cliff are 1 \leq cliff \leq (g-1)//2.
   SeeAlso
    carpet
///
doc ///
   Key
    FineGrading
   Headline
    Option for carpet, canonicalCarpet
   Description
    Text
     The default is FineGrading => false. If the option FineGrading=>true is given, then the 
     ideal returned has the natural ZZ^4 grading, where x_i has degree \{1,0,i,a-i\}\ and 
     y_i has degree \{0,1,i,b-i\}. 
     (Note that after the call carpet(a1,a2) we have a = min(a1,a2), b = max(a1,a2).)
///
doc ///
   Key
    carpet1
    (carpet1, ZZ, ZZ)
    [carpet1, Characteristic]
   Headline
    Ideal of the unique Gorenstein double structure on a 2-dimensional scroll
   Usage
    I = carpet1(a1,a2)
   Inputs
    a1:ZZ
    a2:ZZ
   Outputs
    I:Ideal
   Consequences
    Item
     Creates the carpet over a new ring. The characteristic is given by the option, defaulting to 32003.
   Description
    Text
     Creates a scroll and calls the routine gorensteinDouble to create the carpet. Even for modest size examples,
     this is much slower than the script "carpet", but gives a reassuring check that we have the
     righ computation.
   SeeAlso
    gorensteinDouble
///
doc ///
   Key
    gorensteinDouble
    (gorensteinDouble,Ideal)
   Headline
    attempts to produce a Gorenstein double structure J subset I
   Usage
    gorensteinDouble I
   Inputs
    I:Ideal
   Outputs
    J:Ideal
   Description
    Text
     Let S = ring I, and that I is an ideal of codimension c.
     Let F be the S-free resolution of S/I.
     Assuming that S is a polynomial ring and S/I is Cohen-Macaulay, 
     the canonical module of S/I is 
     omega = coker transpose F.dd_c. The script returns the ideal J that is the kernel of the first
     element of Hom(I, omega). In case I is the ideal of a scroll there is a unique
     element of minimal degree, and it represents a surjection, so S/J is Gorenstein.
   SeeAlso
    carpet1
///


TEST///
assert( betti res carpet1(2,5) == (new BettiTally from {(0,{0},0) => 1, (1,{2},2) => 15, (2,{3},3) => 35, (2,{4},4) => 14, (3,{4},4) => 35,
     (3,{5},5) => 35, (4,{5},5) => 14, (4,{6},6) => 35, (5,{7},7) => 15, (6,{9},9) => 1}) )
assert(false == (betti res canonicalCarpet(7,3,Characteristic =>0) == 
	        betti res canonicalCarpet(7,3,Characteristic =>2)))
assert(isHomogeneous carpet(2,4,FineGrading=>true))
assert(isHomogeneous canonicalCarpet(7,3,FineGrading=>true))
///

end--
restart
uninstallPackage "K3Carpets"
installPackage "K3Carpets"
check "K3Carpets"
viewHelp K3Carpets
---

---FRANK: START HERE
restart
needsPackage "K3Carpets"

--all Cliff=2 examples have a clear pattern 
homotopyRanks(6,2)
homotopyRanks(7,2)

--Cliff = 3,4 g\geq : more mysterious
homotopyRanks(7,3)
(F,h0) = canonicalHomotopies(7,3);
betti res fixedSyzygyScheme (F,2,map(F_2,,syz h0(0,2)))

--here are the homotopies separated by fine grading:
(F,h0) = canonicalHomotopies(7,3, FineGrading=>true);
h0(0,2)
--
homotopyRanks(8,3)
homotopyRanks(9,3)
--
homotopyRanks(8,4)
homotopyRanks(9,4)
--homotopyRanks(10,4) -- slow.

--the following is too slow to use!
loadPackage"kGonalNodalCurves"
g = 6; cliff = 3
I = idealOfNodalCurve(cliff,g,1000)
betti (F =res I)
ff = F.dd_1;
H = makeHomotopies1(ff,F,1);
netList apply(numcols ff, i->{ff_i, apply(g-2, m->(rank h0(i,m+1)))})
