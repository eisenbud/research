//////////

/*
function my_power_min(I, e)
    if e eq 1 then
	return I;
    elif IsOdd(e) then
	IB := MinimalBasis(I);
	JB := MinimalBasis(my_power(I, e - 1));
	return Ideal([f*g: f in IB, g in JB]);
    else
	JB := MinimalBasis(my_power(I, e div 2));
	return Ideal([f*g: f, g in JB]);
    end if;
end function;
*/

function my_power(I, e)
    // IB := MinimalBasis(I);
    IB := GroebnerBasis(I);
    J := I;
    for i := 2 to e do
	// JB := MinimalBasis(J);
	JB := GroebnerBasis(J);
	J := Ideal([f*g: f in IB, g in JB]);
    end for;
    return J;
end function;

//It seems to me that the following only gives the right answer some of the time,
//though it is ok for the case where LP consists of a complement, in the space of
//linear forms, of the last variable, since then
//the power of the last variable that occurs is the regularity of the ideal.
/*function relative_regularity(LP, I, d)
    LPd := my_power(LP, d);
    ILPd := I+LPd;
    assert IsZeroDimensional(ILPd);
    return Max([Degree(f): f in GroebnerBasis(ILPd)]) - d;
end function;
*/


function CastelNuovoMumfordRegularity0(J)
     //compute the regularity of a zero-dimensional ideal J in a polynomial ring
     assert IsZeroDimensional(J);
     P := Generic(J);
     LT := [LeadingTerm(f) : f in GroebnerBasis(J)];
     R := P/Ideal(LT);
     t := Max([Degree(m) : m in LT]); //the smallest possible regularity
     while (Min([0 eq R!m : m in MonomialsOfDegree(P,t)]) eq false) do
         t := t+1;
     end while;
return t;
end function;

function relative_regularity(LP, I, d)
    LPd := my_power(LP, d);
    ILPd := I+LPd;
    assert IsZeroDimensional(ILPd);
    return CastelNuovoMumfordRegularity0(ILPd)-d;
end function;


function rees_ideal(R, LP, nzd)

    n := Rank(R);
    I := DivisorIdeal(R);
    P := Generic(I);
    k := BaseRing(P);

    M:=sub<EModule(R, 1) | [[f]: f in Basis(LP)]>;
    SB := MinimalBasis(MinimalSyzygyModule(M));

    r := #Basis(LP);
    PZ := PolynomialRing(k, n + r, "grevlex");
    AssignNames(
	~PZ, [Sprint(P.i): i in [1..n]] cat [Sprintf("z%o", i): i in [1..r]]
    );
    f := hom<P -> PZ | [PZ.i: i in [1 .. n]]>;
    IZ := Ideal(f(Basis(I)));
    RZ := PZ/IZ;
    phiz := Matrix([[f(v[j]): j in [1..Ncols(v)]]: v in SB]);
    zmat := Matrix([[PZ.(n + j)]: j in [1..r]]);
    mat := phiz*zmat;
    J := IZ + Ideal(Eltseq(mat));
    S := PZ/J;
    g := f(nzd);
    return Saturation(J, g), f;

end function;

//////////
/* This function seems to be defined (better) in set_degrees
function BettiRes(res,first_wts)
// Returns a matrix giving the betti numbers for a free resolution res &
// the column weight corresponding to the top-left entry.
//  The form is as follows (note a free res is assumed to start and
//    end with the zero module), for, eg, the resolution
//  0 <- S(-1)+2S(-2) <- 3S(-2)+4S(-4) <- 5S(-5) <- 0
//    return is [ 1, 3, 0 ]
//		[ 2, 0, 0 ]
//		[ 0, 4, 5 ]
//  and for the (non- minimal) resolution
//  0 <- S(-2) <- S(-2)+2S(-3) <- S(-3)+S(-4) <- 0
//    return is [ 0, 1, 1 ]
//		[ 1, 2, 1 ]
//   ie the top line <-> S(a-j) multiplicity in the jth place where
//  a is max_j{r+j|S(-r) occurs in the jth place}
//
//  first_wts should be either the betti numbers of the first (non-zero)
//  module of the resolution or 0.
    // first get all weights and build table
    Z := Integers();
    len := #BoundaryMaps(res)-1;
    if first_wts cmpeq 0 then
	vs,us := bettiResolve(BoundaryMap(res,1));
    else
	vs,us := bettiResolveCols(BoundaryMap(res,1), first_wts);
    end if;
    us := [u-1 : u in us];
    all_wgts := [vs,us];
    for i in [2..len-1] do
	_,us := bettiResolveCols(BoundaryMap(res,i),us);
        us := [u-1 : u in us];
        Append(~all_wgts,us);
    end for;

    // build betti table
    min,max := Explode([Min(seq),Max(seq)]) where seq is &cat all_wgts;
    mat := ZeroMatrix(Z,max-min+1,len);
    for i in [1..len], j in all_wgts[i] do
	mat[j-min+1,i] +:= 1;
    end for;
    return mat,min;
end function;
*/
