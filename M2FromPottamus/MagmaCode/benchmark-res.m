function Gor(K, n, d, k: Contract:=false)

P<[x]> := PolynomialRing(K, n, "grevlex");
L := [&+[Random(K)*x[i]: i in [1 .. n]]: c in [1 .. k]];
f := &+[l^d: l in L];

//f := (x[1]+x[2]+x[3])^2;
//f := (x[1]+x[2])^2;
//f := x[1]^2+x[2]^2;
// f;

MQ := [];
XQ := [];
I := {@@};
S := SparseMatrix(K);
row := 0;

for i := 0 to d + 1 do
    M := MonomialsOfDegree(P, i);
    for m in M do

	if Contract then
	    g := Parent(f)!0;
	    for t in Terms(f) do
		l, q := IsDivisibleBy(t, m);
		if l then
		    g +:= q;
		end if;
	    end for;
	else
	    e := Exponents(m);
	    g := f;
	    for j := 1 to #e do
		g := Derivative(g, e[j], j);
	    end for;
	end if;

	Append(~MQ, m);
	Append(~XQ, g);

	gC, gM := CoefficientsAndMonomials(g);
	row +:= 1;
	for gi := 1 to #gM do
	    gm := gM[gi];
	    Include(~I, gm);
	    ind := Index(I, gm);
	    SetEntry(~S, row, ind, gC[gi]);
	end for;
    end for;
end for;

if Nrows(S) lt #MQ then
    r := #MQ;
    SetEntry(~S, r, 1, 1);
    SetEntry(~S, r, 1, 0);
end if;

N := BasisMatrix(Nullspace(S));
B := [&+[N[i, j]*MQ[j]: j in [1 .. #MQ]]: i in [1 .. Nrows(N)]];

return Ideal(B);

end function;

function MinFreeResConj(K, n, d, k)
    P<[x]> := PolynomialRing(K, n, "grevlex");
    M := MonomialsOfDegree(P, d);
    L := [&+[Random(K)*m: m in M]: c in [1 .. k]];
    I := Ideal(L);
    return I;
end function;

function MinFreeResConj1(K, n, d, k)
    return MinFreeResConj(K, n, d, Binomial(n - 1 + d, d) - k);
end function;


/*
n:=10;
for i in [15..2*n] do

I := Gor(GF(32003), n,3,i);
M:=QuotientModule(I);
B:=Matrix(BettiTable(M));
//c:=#[i : i in Eltseq(B[3]) | i eq 0];
c:=Min([j : j in [1..Ncols(B)]  | B[3,j] ne 0])-1;
i,c,B;
end for;

I := MinFreeResConj1(GF(32003), 8,2,4);
M:=QuotientModule(I); time FreeResolution(M);

*/
