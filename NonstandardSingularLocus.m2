--The following code should replace the methods for "singularLocus". Those for
--singularLocus(Ideal) and singularLocus(AffineVariety) are copies of the current ones (v.1.9.1).
--The new code for singularLocus(Ring) checks various conditions for validity
--The new code for singularLocus(ProjectiveVariety) takes into account the possibility
--that the grading of the ring is nonstandard. (Alas, this can be slow!)

   --to replace /Applications/Macaulay2-1.9.1/share/Macaulay2/Core/quotring.m2:301:44-304:74: --source code:
     --/Applications/Macaulay2-1.9.1/share/Macaulay2/Core/varieties.m2:278:35-278:62: --source code:
     singularLocus(AffineVariety) := X -> Spec singularLocus ring X
     ---------------------------------
     -- code for method: singularLocus(Ideal)
     --/Applications/Macaulay2-1.9.1/share/Macaulay2/Core/quotring.m2:306:45-306:71: --source code:
     singularLocus(Ideal) := QuotientRing => (I) -> singularLocus(ring I / I)

   --Code for method singularLocus(Ring)  
     singularLocus(Ring) := QuotientRing => (R) -> (
          f := presentation R;
          A := ring f;
	  K = coefficientRing A;
	  if not isField K and isPolynomialRing A and isCommutative A then error"wrong kind of ring";
	  if char K != 0 then <<"warning: applying Jacobian criterion and char is not 0"<<end;
          A / (ideal f + minors(codim(R,Generic=>true), jacobian presentation R)))
   
   --Code for method: singularLocus(ProjectiveVariety)
   --to replace /Applications/Macaulay2-1.9.1/share/Macaulay2/Core/varieties.m2:272:39-276:76: --source code:
     singularLocus(ProjectiveVariety) := X -> (
          R := ring X;
	  if degreeLength R>1 then error"Needs ring X to have degree length 1";
	  f := presentation R;
          A := ring f;
	  d := lcm flatten((gens A)/degree);	  
	  if not isPolynomialRing A then error"needs ring X to be a quotient of a polynomial ring";
	  if d === 1 then(
              Proj(A / saturate (minors(codim(R,Generic=>true), jacobian f) + ideal f)))
          else (    
    	      B := basis(d,A^1);
    	      n := numcols B;
	      K := coefficientRing A;
    	      t := symbol t;
    	      T := K[t_0..t_(n-1)];
	      g := map(A,T,B);	      
	      h := map(R,T,sub(B,R));
    	      I := ker h;
    	      J = trim g (ideal presentation singularLocus (T/I));
              Proj(A/saturate J))
	  )

TEST///
S0 = QQ[x,y,z]
S = QQ[x,y,z, Degrees =>{2,3,4}]
R = S/ideal(y^4-z^3)
T = singularLocus R
assert(class T === class R)
assert(dim T == 1)

assert(dim singularLocus Proj S0 == -infinity)
assert(dim singularLocus Proj S == 0)
Y = Proj R
Z = singularLocus Y
assert(class Z === class Y)
assert(dim Z == 0)
///

end--

restart
load"NonstandardSingularLocus.m2"

S = QQ[x,y,z, Degrees =>{2,3,4}]
X = Proj S
singularLocus X

--What this should replace:
{*
     /Applications/Macaulay2-1.9.1/share/Macaulay2/Core/varieties.m2:278:35-278:62: --source code:
     singularLocus(AffineVariety) := X -> Spec singularLocus ring X
     ---------------------------------
     -- code for method: singularLocus(Ideal)
     /Applications/Macaulay2-1.9.1/share/Macaulay2/Core/quotring.m2:306:45-306:71: --source code:
     singularLocus(Ideal) := QuotientRing => (I) -> singularLocus(ring I / I)
     ---------------------------------
     -- code for method: singularLocus(ProjectiveVariety)
     /Applications/Macaulay2-1.9.1/share/Macaulay2/Core/varieties.m2:272:39-276:76: --source code:
     singularLocus(ProjectiveVariety) := X -> (
          R := ring X;
          f := presentation R;
          A := ring f;
          Proj(A / saturate (minors(codim(R,Generic=>true), jacobian f) + ideal f)))
     ---------------------------------
     -- code for method: singularLocus(Ring)
     /Applications/Macaulay2-1.9.1/share/Macaulay2/Core/quotring.m2:301:44-304:74: --source code:
     singularLocus(Ring) := QuotientRing => (R) -> (
          f := presentation R;
          A := ring f;
          A / (ideal f + minors(codim(R,Generic=>true), jacobian presentation R)))
*}