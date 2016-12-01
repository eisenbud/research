-- wanting to produce extensions 0 --> B --> E --> A -->0
-- use the fact that there exists an exact sequence 
--  Hom(F_0,B) --> Hom(M,B) --> Ext^1(A,B) --> 0
-- wher M = image F.dd_1 and F and G are respectively resolutions of A and B


pushOut = method()
pushOut(Matrix,Matrix) := (phi,psi) -> (
    -- assume both maps have (literally) the same source
    M := source phi;
    N := source psi;
    if M =!= N then error "expected the same source of both maps"
    	else(
	    	P := target phi;
		Q := target psi; 
		pushOutMatrix := phi || (-psi);
		coker (map(P ++ Q, M, pushOutMatrix))
	    )
    ) 

constructRandomModuleElement = method()
constructRandomModuleElement(Module,ZZ) := (M,d) -> (
    n := numgens M;
    R := M.ring;
    L := flatten entries random(R^1,R^{n:-d}); -- could use random ZZ and a apply function or what not 
    	    	       	       	       	       -- to get random elements in degrees up to d.
    rdmElt:= sum apply(n, i -> (L#i) * M_{i});
    rdmElt
    )
 

constructRandomExtensions = method()
constructRandomExtensions(ZZ,ChainComplex,ChainComplex) := (d,F,G) -> (
    B := coker G.dd_1;
    A := coker F.dd_1;
    M := image F.dd_1;
    Z := Hom(M,B);
    phi := inducedMap(F_0,M,id_(M));
    psi := map(B, M, homomorphism constructRandomModuleElement(Z,d));
    E := pushOut(phi,psi);
    rowOfzeros = apply(rank ambient B, i-> 0);
  iota :=   map(E,B,  (matrix apply(rank F_0, i -> rowOfzeros)) || id_(G_0) )  ;
  p := map(A, E, matrix drop(entries id_E, - rank ambient B));
  chainComplex{p,iota}
)

-- To check if an extension is trivial we compute its
-- image under the map Hom(M,B) -> Hom(M,B) / Hom(F_0,B)
-- we assume that the extension is given by Hom(M,B) which
-- we regard as a matrix
-- also want to assume given the resolutions.
-- the method takes a list of elements of the ring as input
-- the downside is that we need to know the number of generators of Hom(M,B)
-- should fix this 
isExtensionTrivial = method()
isExtensionTrivial(List,ChainComplex,ChainComplex) := (L,F,G) -> (
    B := coker G.dd_1;
    M := image F.dd_1;
    j := inducedMap(F_0, M, id_(M));
    Z := Hom(M,B);
    delta := inducedMap(coker Hom(j,B), Hom(M,B), id_(Hom(M,B))); 
    (delta * (sum apply(numgens Z, i -> (L#i) * Z_{i}))) == 0
)




