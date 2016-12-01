function bettiResolveCols(M,vs, weights: Check)
// for an m*n matrix of homogeneous polynomials M, as in
// bettiResolve except that the vs are already known and
// passed in as an argument.
    if Type(M) eq ModMPolHom then
	M := Matrix(M);
    end if;
   nw:= #weights;
    nr := Nrows(M); nc := Ncols(M);
    assert #vs eq nc;

    us := [Integers()|];
    for j in [1..nr] do Undefine(~us,j); end for;

    for i in [1..nr], j in [1..nc] do
	f := M[i, j];
    	if not IsZero(f) then
	    deg := &+[weights[i]*e[i] : i in [1..nw]] where
		e:=Exponents(LeadingTerm(M[i,j])); 
	    if IsDefined(us, i) then
		error if deg ne (us[i]-vs[j]), "Input vs are invalid";
	    else
		us[i] := vs[j]+deg;
		if not Check then
		    break;
		end if;
	    end if;
	end if;
    end for;

    if not ((#us eq nr) and IsComplete(us)) then
			//some zero rows - fill in with some small weight
	val := (#us eq 0) select 0 else Min(Seqset(us))-1;
        for i in [1..nr] do
	    if not IsDefined(us,i) then us[i] := val; end if;
	end for;
    end if;
    return vs,us;

end function;

function BettiRes(res,first_wts, weights: Check)
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
//    if first_wts cmpeq 0 then
//	vs,us := bettiResolve(BoundaryMap(res,1));

	vs,us := bettiResolveCols(
	    BoundaryMap(res,1), first_wts,weights: Check := Check
	);
    us := [u-1 : u in us];
    all_wgts := [vs,us];
    for i in [2..len-1] do
	_,us := bettiResolveCols(BoundaryMap(res,i),us,weights: Check := Check);
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

function regBettiRes(BT,topLeft)
	 return Nrows(BT) + topLeft;
end function;

/*function z_degrees(L)
//L is a list of indices
	 return &+[

end function;
*/

/*
P<x,z> := PolynomialRing(GF(2),2,"grevlex");
i:=(Ideal([x,z]))^2;
F:=FreeResolution(GradedModule(i));

BettiRes(F,[0],[0,1]);
*/

