
-----------------------------------------------
-- Translation to Magma -----------------------
-----------------------------------------------

toMagma = method()
toMagma Ring := (R) -> (
     -- note: R is assumed to be a polynomial ring.  Variables alowed: single letters, 
     -- letters indexed by a single non-negative integer.
     -- For now the base ring needs to be ZZ/p or QQ.
     kk := coefficientRing R;
     p := char kk;
     basering := if p === 0 then "RationalField()" else "GF("|p|")";
     "R<" | concatenate between(",", (gens R)/toString) | "> := PolynomialRing(" 
       | basering | "," | toString numgens R | ",\"grevlex\");"
     )
toMagma Ideal := (I) -> (
     a := "I := ideal< R | \n   ";
     g := concatenate between(",\n   ", apply(numgens I, i -> toString I_i));
     a | g | ">;\n" 
     )

magmaICstring = "time Js := Normalization(@I@);\n"

magmaIntegralClosure = method()
magmaIntegralClosure String := (idealName) -> 
     replace("@I@",idealName,magmaICstring)

runMagmaGB = method()
runMagmaGB Ideal := (I) -> (
     "foo" 
     << toMagma ring I << endl
     << toMagma I
     << "time J := GroebnerBasis(I);\n"
     << "#Js;\n"
     << "quit;\n" << close;
     run "magma <foo"
     )

runMagmaIntegralClosure = method()
runMagmaIntegralClosure Ideal := (I) -> (
     "foo" 
     << toMagma ring I << endl
     << toMagma I
     << "time Js := Normalization(I);\n"
     << "#J;\n"
     << "quit;\n" << close;
     run "magma <foo"
     )

runMagmaDimension = (filestring, I) -> (
     fi := filestring;
     openOut fi;
     fi << toMagma ring I << endl ;
     fi << toMagma I;
     fi << "time Dimension(I);";
     fi << close;
     )
     
MakeMagmaIdealList = (S1) -> (
     fi := "P4Surfaces.m";
     openOut fi;
     fi << toMagma ring S1#((keys S1)_0) << "\n" ;
     fi << "[";
     apply(keys S1, k -> 
	  fi << "[" << k<< "," << toMagma(S1#k) << "]" <<  ",\n");
     fi << "]";
     fi << close;
     )
end

restart
load "toMagma.m2"
S = ZZ/101[a,b,c]
I = ideal"a2,b2"
runMagmaDimension("foo", I)
ideal singularLocus I
I + minors(2, jacobian I)
print toMagma R; print toMagma I
runMagmaGB I

{* -- magma
R<x_1,x_2,x_3,x_4,x_5,x_6,x_7,x_8,x_9,x_10,x_11,x_12,x_13,x_14,x_15,x_16,x_17,x_18,x_19,x_20,x_21,x_22,x_23,x_24,x_25,x_26,x_27,x_28,x_29,x_30,x_31,x_32> := PolynomialRing(GF(32003),32,"grevlex");
I := ideal< R | 
   -x_16*x_28+x_12*x_32,
   -x_15*x_27+x_11*x_31,
   -x_14*x_26+x_10*x_30,
   -x_13*x_25+x_9*x_29,
   -x_8*x_20+x_4*x_24,
   -x_7*x_19+x_3*x_23,
   -x_6*x_18+x_2*x_22,
   -x_5*x_17+x_1*x_21,
   -x_24*x_31+x_23*x_32,
   -x_24*x_30+x_22*x_32,
   -x_23*x_30+x_22*x_31,
   -x_24*x_29+x_21*x_32,
   -x_23*x_29+x_21*x_31,
   -x_22*x_29+x_21*x_30,
   -x_20*x_27+x_19*x_28,
   -x_20*x_26+x_18*x_28,
   -x_19*x_26+x_18*x_27,
   -x_20*x_25+x_17*x_28,
   -x_19*x_25+x_17*x_27,
   -x_18*x_25+x_17*x_26,
   -x_24*x_31+x_23*x_32,
   -x_22*x_29+x_21*x_30,
   -x_20*x_27+x_19*x_28,
   -x_18*x_25+x_17*x_26,
   -x_24*x_30+x_22*x_32,
   -x_23*x_29+x_21*x_31,
   -x_20*x_26+x_18*x_28,
   -x_19*x_25+x_17*x_27,
   -x_18*x_19+x_17*x_20+x_20*x_21-x_19*x_22-x_18*x_23-x_22*x_23+x_17*x_24+x_21*x_24+x_20*x_25+x_24*x_25-x_19*x_26-x_23*x_26-x_18*x_27-x_22*x_27-x_26*x_27+x_17*x_28+x_21*x_28+x_25*x_28+x_20*x_29+x_24*x_29+x_28*x_29-x_19*x_30-x_23*x_30-x_27*x_30-x_18*x_31-x_22*x_31-x_26*x_31-x_30*x_31+x_17*x_32+x_21*x_32+x_25*x_32+x_29*x_32>;
time J := GroebnerBasis(I);
*}
