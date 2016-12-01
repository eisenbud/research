//Code to compute the maximum regularity of a fiber of
//the projection of a variety of dimension n defined by the homogeneous
//ideal I, to PP^{n+c}
load "Rees.m";
load "set_degrees.m";

//NOTE: this isn't quite correct; need to test the power of LP equal
//to max(reg I, y-reg of rees algebra)

function MaxFiberReg(I,c)
     // I is an ideal of the polynomial ring P
     P := Generic(I);
     k := CoefficientRing(P);
     dimI := Dimension(I); //Krull dimension of P/I
     regI := 1+Regularity(GradedModule(I));

     print BettiTable (FreeResolution(GradedModule(I)));
     print(regI); 

     //compute the Rees algebra of a sequence of general linear forms
     M := MonomialsOfDegree(P,1);
     LP := Ideal([&+[Random(k)*m: m in M]: i in [1 .. dimI+c]]);
     //Find the y-regularity of the Rees ring of LP mod I
     R:=P/I;
     nzd := R!M[1];
     ri, f := rees_ideal(R, LP, nzd);
     PZ := Codomain(f);
     M := GradedModule(ri);

     //The Rees resolution
     print "computing the resolution of the Rees algebra";
     time res := MinimalFreeResolution(M);

     //The "y-regularity" (this should be much faster than it is)
     print "computing the y-regularity";
     weights := [0 : i in [1..Rank(P)]] cat [1 : i in [1..dimI+c]];
     time BT,topLeft := BettiRes(res,[0],weights);

     //Report
     print BT;
     rB := regBettiRes(BT, topLeft)-1; 
     r := Max([regI,rB]);
     print "computing the relative regularity" ;
     print "of the ",r,"-th power of the linear ideal";
     
     ans := relative_regularity(LP, I, r)+1;
     print "maximum regularity of a fiber is";
     print ans;
     return(ans);

     end function;

/*
load "MaxFiberReg.m";
k:=GF(32003);
P<x_0,x_1,x_2,x_3,x_5> := PolynomialRing(k,5,"grevlex");
//form the ideal gen by 3 random cubics:
     M := MonomialsOfDegree(P,3);
     I := Ideal([&+[Random(k)*m: m in M]: i in [1 .. 3]]);

time MaxFiberReg(I,1);
time MaxFiberReg(I,3);
time MaxFiberReg(I,2);

I := eval Read("ab.d10.g6");
time MaxFiberReg(I,1);
*/



