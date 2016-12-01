ExpectedBettiMRC := function(r,m)

//The "expected" Betti table of the smallest regularity
//quotient ring of the polynomial ring in r variables having length m.
//The ideal of such a ring is obtained by adding a general linear form
//to the ideal of m general points in P^r. However, ideals obtained that
//way do NOT always have the expected betti table (smallest example is 11 points
//in P^6, as originally predicted by the "Minimal Resolution Conjecture". See the
//papers of Eisenbud-Popescu and Eisenbud-Popescu-Schreyer-Walter on this subject
//for the known range of counterexamples. THERE IS PRESENTLY NO EXAMPLE KNOWN where
//the general zero-dimensional ring of this type does NOT have expected Betti table.

e:=1;
while(Binomial(r+e,e) le m) do e := e+1; end while;
d := e-1;
a := m-Binomial(r+d,d);
toprow := [0] cat [Max((Binomial(d+i-1,i-1))*(Binomial(r+d,d+i)) - a*(Binomial(r,i-1)), 0) : i in [1..r]];
bottomrow :=[0] cat [Max(a*(Binomial(r,i))-(Binomial(d+i,i))*Binomial(r+d,d+i+1), 0) : i in [1..r]];
N := Matrix([[1] cat [0 : j in [1..r]]]);

if (d ge 2) then
    N1 := Matrix([[0 : j in [0..r]] : i in [2..d]]);
    N := VerticalJoin(N,N1);   
end if;
    
M := Matrix([toprow,bottomrow]);
return(VerticalJoin(N,M));

end function;

ExpectedBettiMRC1 := function(n,d,k)
//Like ExpectedBetti, but starts from the degree d of the (lowest degree)
//generators of the ideal and the codimension k of the ideal in that degree.
d:=d-1;
r := n;
m := &+[Binomial(r-1+i,i) : i in [0..d]]+k;
a := m-Binomial(r+d,d);
toprow := [0] cat [Max((Binomial(d+i-1,i-1))*(Binomial(r+d,d+i)) - a*(Binomial(r,i-1)), 0) : i in [1..r]];
bottomrow :=[0] cat [Max(a*(Binomial(r,i))-(Binomial(d+i,i))*Binomial(r+d,d+i+1), 0) : i in [1..r]];
N := Matrix([[1] cat [0 : j in [1..r]]]);

if (d ge 2) then
    N1 := Matrix([[0 : j in [0..r]] : i in [2..d]]);
    N := VerticalJoin(N,N1);   
end if;
    
M := Matrix([toprow,bottomrow]);
return(VerticalJoin(N,M));

end function;

ebm := ExpectedBettiMRC;
ebm1 := ExpectedBettiMRC1;

//An example that is is a counterexample to the "old" MRC conjecture,
//but not the "new" one: 11 points in P6

//"Two ways of parametrizing the same example:"
A := ebm1(6,2,4);
B := ebm(6,11);

load "benchmark-res.magma";

//The actual resolution:
I := MinFreeResConj1(GF(32003), 6, 2, 4);
M:=QuotientModule(I); 
C:= Matrix(BettiTable(FreeResolution(M)));

assert(A eq B);
assert(A eq C);

