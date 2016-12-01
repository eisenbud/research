load "MaxFiberReg.m";
load "SurfaceNames.m";

/*
//Code to Test dimension, degree, smoothness of each example
//With the correct characteristics, they all pass.

//time for i in [1..#SurfaceNames] do
//N := SurfaceNames[i];

time for N in SurfaceNames do
//for N in [ "enr.d11.g10", "bielliptic.d15.g21", "bielliptic.d10.g6" ] do
print N;
I := eval Read(N);

if N eq "enr.d11.g10" then 
    p:=43;
elif N eq "bielliptic.d15.g21" or N eq "bielliptic.d10.g6" then 
    p:=911;
else 
    p:=31991;
end if;
I := ChangeRing(I, GF(p));

D:= Dimension(I);
if not D eq 3 then 
error("Error: Not a surface");

else
    //Now compute the degree of the putative surface
    //P:=HilbertPolynomial(I);
    //deg := Factorial(Degree(P))*LeadingCoefficient(P);
deg := Degree(Scheme(Proj(Generic(I)),I));
print deg;

   //test for nonsingularity
MI := JacobianMatrix(Basis(I));
BJ1 := Minors(MI,2);
J1:=Ideal(BJ1);
J := I+J1;

  if not Dimension(J) eq 0 then
   error("This surface is singular");
   end if;

end if;
end for;
*/

/*
//The following code uses "MaxFiberReg.m" to compute
//the maximum regularity of the fiber of generic projection
//to P3 for each surface in the list of 48.
L := [];
Lspecial := [];
count := 0;
	//for N in ["bielliptic.d10.g6"]do
        //for N in ["elliptic.scroll"]do
time for N in SurfaceNames do
      count := count+1;
print N;
print "surface number is";
print count;
I := eval Read(N);
time ans := MaxFiberReg(I,1);
if ans le 2 then
print "regularity <= 2";
//print BettiTable(FreeResolution(GradedModule(I)));
Lspecial := Lspecial cat [N];
end if;
L := L cat [ans];
end for;
Lspecial;
L;
/*
Lspecial := [ cubicscroll, castelnuovo, ell.d7.g6, elliptic.scroll ];
[ 3, 3, 3, 3, 3, 3, 3, 3, 2, 3, 3, 3, 3, 3, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2,
3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 3, 3, 3, 3, 3, 3, 3 ];

for N in Lspecial do
I := eval Read(N);
print Matrix(BettiTable(FreeResolution(GradedModule(I))));

end for;
*/
/*
[1 0 0]
[0 3 2]

[1 0 0]
[0 1 0]
[0 2 2]

[1 0 0]
[0 1 0]
[0 0 0]
[0 2 2]

[1 0 0 0]
[0 0 0 0]
[0 5 5 1]
*/
/*
if N eq "enr.d11.g10" then 
    p:=43;
elif N eq "bielliptic.d15.g21" or N eq "bielliptic.d10.g6" then 
    p:=911;
else 
    p:=31991;
end if;
I := ChangeRing(I, GF(p));
*/


//The following code checks whether the y-regularity of the Rees ideal is
 //equal to the degree of the surface (equivalently, the regularity
 //of the special fiber) in each case.
count := 0;
	//for N in ["bielliptic.d10.g6"]do
        //for N in ["elliptic.scroll"]do
time for N in SurfaceNames do
      count := count+1;
print count;
print N;
I := eval Read(N);
     P := Generic(I);
     k := CoefficientRing(P);
     deg := Degree(Scheme(Proj(Generic(I)),I));

     //compute the Rees algebra of a sequence of general linear forms
     M := MonomialsOfDegree(P,1);
     LP := Ideal([&+[Random(k)*m: m in M]: i in [1 .. 4]]);

     //Find the y-regularity of the Rees ring of LP mod I
     R:=P/I;
     nzd := R!M[1];
     ri, f := rees_ideal(R, LP, nzd);
     PZ := Codomain(f);
     M := GradedModule(ri);

     //The Rees resolution
     res := MinimalFreeResolution(M);

     //The "y-regularity" (this should be much faster than it is)
     weights := [0 : i in [1..Rank(P)]] cat [1 : i in [1..4]];
     BT,topLeft := BettiRes(res,[0],weights);
rB := regBettiRes(BT, topLeft); //y-regularity regularity of the ideal
print [rB, deg];
assert(rB eq deg);
end for;

