k:=GF(32003);
n:=5;
P<[x]>:=PolynomialRing(k,n,"grevlex");
LP := ideal <P | [x[i] : i in [1..n]]>;

/*
The following is correct. But there's trouble
if we use P instead of P/(0).
*/
R:=P/(Ideal(P!0)); R;
ri, f := rees_ideal(R,LP, P.1); ri;

