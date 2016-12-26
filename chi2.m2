       newPackage(
               "Chi2",
               Version => "0.1", 
               Date => "Dec 24, 2016",
               Authors => {{Name => "David Eisenbud", 
                         Email => "de@msri.org"}},
               Headline => "Implement Chi2",
               DebuggingMode => true
               )

       export {
	   "tau",
	   "reverseFactors"
	   }
///
restart
uninstallPackage"Chi2"
installPackage"Chi2"
check "Chi2"
viewHelp Chi2
///
       -- Code here



tau = method()
tau(Module, Module, ZZ,ZZ) := (P,Q,s,t) ->(
    --regarding P as degree s and Q as degree t, produce the natural map
    --P**Q --> Q**P.
    S := ring P;
    p := rank P;
    q := rank Q;
    sgn := (-1)^(s*t);
    m := mutableMatrix(S,q*p,p*q);

    apply(p, i-> apply(q, j->
	    m_(j*p+i, i*q+j) = 1));
    ta := sgn*matrix m;
    map(Q**P,P**Q,ta)
    )

reverseFactors = method()
reverseFactors(ChainComplex, ChainComplex) := (F,G) ->(
    --define the iso (F**G --> G**F)
    tar := G**F;
    sour := F**G;
    Ln := symbol Ln;
    phi := for n from min sour to max sour list (
	Ln = for i from max(min G,n-max F) to min(max G,n-min F) list (
    	(tar_n)_[(i,n-i)]*tau(F_(n-i),G_i,n-i,i)*(sour_n)^[(n-i,i)]); 
    	sum Ln);
map(tar,sour,n->phi_(n-min sour))
    )


beginDocumentation()
       doc ///
       Key
         Chi2
       Headline
         Adams Operation
       Description
         Text
	  Used in Walker's proof of Buchsbaum-Eisenbud-Horrocks
	  conjecture that the sum of the betti numbers is exponential
       ///
       TEST ///
       -- test code and assertions here
       -- may have as many TEST sections as needed
       ///
doc ///
   Key
    reverseFactors
    (reverseFactors, ChainComplex, ChainComplex)
   Headline
    the isomorphism from F**G to G**F when F,G are complexes
   Usage
    phi = reverseFactors(F,G)
   Inputs
    F:ChainComplex
    G:ChainComplex    
   Outputs
    phi:ChainComplexMap
     to G**F from F**G
   Description
    Text
     maps F_(n-i)**G_i \to G_i**F_(n-i) changing the basis order and putting in sign (-1)^(i*(n-i)).
    Example
     S = ZZ/101[a,b]
     F = chainComplex{map(S^1,S^{-1},a)}
     G = chainComplex{map(S^1,S^{-1},b)}[3]
     phi = reverseFactors(F,G)
     G**F
     F**G
     --is it a map of complexes?
     apply(1+length(F**G), i->(
		 (phi_i)*((F**G).dd_(i+1)) ==  ((G**F).dd_(i+1))*phi_(i+1)
		 ))
     --Does reverseFactors create an isomorphism?
     apply(length (F**G), i -> (rank phi_i) == rank ((F**G)_i))
///
     
TEST///
S = ZZ/101[a]
P= S^{0,1}
Q = S^{3,5}
s = 1;t=1
ta = tau(P,Q,s,t)
assert isHomogeneous ta
assert (tau(P,Q,s,t)*tau(Q,P,s,t) == id_(Q**P))
///

TEST///
S = ZZ/101[a,b,c]
M = S^1/ideal{a^2,b^2,c^2}
N = S^1/((ideal gens S)^3)
betti(F = complete res M)
betti (G = complete res N)
phi = reverseFactors(F,G);
--is it a map of complexes?
assert all(apply(1+length(F**G), i->(
(phi_i)*((F**G).dd_(i+1)) ==  ((G**F).dd_(i+1))*phi_(i+1)
)),i->i == true)
--Does reverseFactors create an isomorphism?
assert all(apply(length (F**G), i -> (rank phi_i) == rank ((F**G)_i)), i->i==true)
///

end--
restart
uninstallPackage"Chi2"
installPackage"Chi2"
check "Chi2"
viewHelp Chi2
