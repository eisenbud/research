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
	   "eulerCharacteristic",
	   "evenEulerCharacteristic",
	   "oddEulerCharacteristic",	   	   
	   "reverseFactors",
	   "sym2",
	   "wedge2",
	   "chi2",
	   "excess",
	   "Walker"
	   }
///
restart
uninstallPackage"Chi2"
installPackage"Chi2"
check "Chi2"
viewHelp Chi2
///



reverseFactors = method()
reverseFactors(Module, Module, ZZ,ZZ) := (P,Q,s,t) ->(
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

reverseFactors(ChainComplex, ChainComplex) := (F,G) ->(
    --define the iso (F**G --> G**F)
    tar := G**F;
    sour := F**G;
    Ln := symbol Ln;
    phi := for n from min sour to max sour list (
	Ln = for i from max(min G,n-max F) to min(max G,n-min F) list (
    	(tar_n)_[(i,n-i)]*reverseFactors(F_(n-i),G_i,n-i,i)*(sour_n)^[(n-i,i)]); 
    	sum Ln);
map(tar,sour,n->phi_(n-min sour))
    )

sym2 = method()
sym2 ChainComplex := F ->(
    tau := reverseFactors(F,F);
    G := F**F;
    Gs := image(id_(F**F)+tau);
    GGs := chainComplex(for i from min Gs+1 to max Gs list prune Gs.dd_i);
    GGs[-min G]) 

wedge2 = method()
wedge2 ChainComplex := F ->(
    tau := reverseFactors(F,F);
    G := F**F;
    Gs := image(id_(F**F)-tau);
    GGs := chainComplex(for i from min Gs+1 to max Gs list prune Gs.dd_i);
    GGs[-min G])

evenEulerCharacteristic = F ->  sum for i from min F to max F list if even i then degree HH_i F else 0
oddEulerCharacteristic = F ->  sum for i from min F to max F list if odd i then  degree HH_i F else 0
eulerCharacteristic = F ->  sum for i from min F to max F list (-1)^i* degree HH_i F

chi2 = F -> eulerCharacteristic sym2 F - eulerCharacteristic wedge2 F

excess = method()
excess ChainComplex := F ->(
    excess1a := 2*oddEulerCharacteristic sym2 F;
    excess1b := 2*evenEulerCharacteristic wedge2 F;
    G := F**F;
    excess2 := -sum(for i from min G to max G list degree HH_i(G)) +
         (degree HH_0 F)*sum(for i from min F to max F list rank F_i);
    (excess1a, excess1b,excess2))
excess Module := M ->(
    F := res M;
    excess F)

Walker = M ->(F:=res M; 
    sumbetti = sum(for i from min F to max F list rank F_i);
    (2^(codim M)*degree M + sum toList (excess M)) == (degree M)*sumbetti)

///

--installPackage"Chi2"
viewHelp Chi2

restart
loadPackage("Chi2", Reload=>true)
S = ZZ/101[a,b,c]
mm = ideal vars S
excess(S^1/(mm^2))
F = res(mm^2)


M = S^1/mm^2
Walker M
sum toList excess(S^1/mm^2)

e = eulerCharacteristic F
eulerCharacteristic (F**F)
evenEulerCharacteristic(F**F)
oddEulerCharacteristic(F**F)
eulerCharacteristic (F**F)
eulerCharacteristic (wedge2 F)
eulerCharacteristic (sym2 F)
apply(length (F**F), i->degree HH_i(F**F))
chi2 F
///

beginDocumentation()
       doc ///
       Key
         Chi2
       Headline
         Symmetric and exterior squares of a complex
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
    (reverseFactors, Module, Module, ZZ,ZZ)    
   Headline
    The isomorphism from F**G to G**F when F,G are complexes
   Usage
    phi = reverseFactors(F,G)
    phi = reverseFactors(M,N,p,q)
   Inputs
    F:ChainComplex
    G:ChainComplex    
    M:Module
    N:Module
    p:ZZ
    q:ZZ
   Outputs
    phi:ChainComplexMap
     to G**F from F**G
   Description
    Text
     maps F_(n-i)**G_i \to G_i**F_(n-i) changing the basis order and putting in sign (-1)^(i*(n-i)).
     In the case of modules, p and q specify the homological degrees of M and N respectively. This is
     used to construct the map of complexes, the general case.
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

--Walker's inequality:
--If F is  a resolution of a module M of finite length, then
--(2^(codim M)*degree M + 2*(oddEulerCharacteristic sym2 F + evenEulerCharacteristic wedge2 F) = 
--sum(for i from min F**F to max F**F i-> degree HH_i(F**F)) <= (degree M)*sum(for i from min F to max F list rank F_i)

M = 
