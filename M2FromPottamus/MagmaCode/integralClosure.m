
function RandomPoly(P,d)
    
    kk:=BaseRing(P);
    R := CoordinateRing(P);
    B:=MonomialsOfDegree(R,d);
    return &+[Random(kk)*b : b in B];

    end function;
function RandomIdeal(P,L)
    return Ideal([RandomPoly(P,d) : d in L]);
    end function;

//function ProjectionFromSubspace
n:=3;
P<[x]>:=ProjectiveSpace(GF(32003), n);
C := Scheme(P,RandomIdeal(P,[3 : i in [1..n-1]]));
//When we used n equations (n= 5) of degree 3, getting a non-rational point,
//the program stalled on the last step of the projection.
//Also with 4 equations in P5, couldn't seem to get plane curve.



Dimension (C);
Degree(C);
ArithmeticGenus(C);
SetVerbose("IsoToSub",1);
C3:=IsomorphicProjectionToSubspace(C);

q := Ambient(C3)!([1,0,0,0]);
D,pi := Projection(C3,q);
AssignNames(~D, ["a"cat IntegerToString(i) : i in [1..3]]);
// gives internal names for the vars of the ambient ring of D

//time Genus(Curve(D)); //.1 sec
D1<a,b>:=AffinePatch(D,1);
J:=Ideal(AffinePatch(D,1));

//Normalization works on an ideal gen by one poly in 2 vars (or the poly itself)
SetVerbose("IntCl",1);
M:=Normalization(J);
K:=M[1][1]; //affine ideal of the normalized curve
AssignNames(~K, ["u","v","w"]);
f := M[1][2]; //inclusion map of k[a,b] to ambient ring of the normalization.
GB:=GroebnerBasis(K);
K1:=ChangeOrder(K, "grevlex");

D:=RandomCurveByGenus(7, Rationals());
//time Genus(Curve(D)); // sec
D1<a,b>:=AffinePatch(D,1);
J:=Ideal(AffinePatch(D,1));

//Normalization works on an ideal gen by one poly in 2 vars (or the poly itself)
SetVerbose("IntCl",1);
time M:=Normalization(J); // 9.2 sec for the case of genus 7 over Q.
K:=M[1][1]; //affine ideal of the normalized curve
AssignNames(~K, ["t","u","v","w"]);
f := M[1][2]; //inclusion map of k[a,b] to ambient ring of the normalization.
//print "about to compute the lex GB";  //This turns out to be slow!
//time GB:=GroebnerBasis(K);
//K1:=ChangeOrder(K, "grevlex");
//#Basis(K1);

K<x1,x2>:=RationalFunctionField(GF(101),2);
L<a> := RationalFunctionField(K); //this const gives the "univariate dense func fld"
R<b> := PolynomialRing(L); //this const gives univariate
f:=a^3+b^5+1;
F:=ext<L|f>;
Rbar := MaximalOrderFinite(F); Rbar;


error "";

D:=Curve(Spec(Rbar), f);
   
//Normalization works on an ideal gen by one poly in 2 vars (or the poly itself)
SetVerbose("IntCl",1);
M:=Normalization(J);
K:=M[1][1]; //affine ideal of the normalized curve
AssignNames(~K, ["u","v","w"]);
f := M[1][2]; //inclusion map of k[a,b] to ambient ring of the normalization.
