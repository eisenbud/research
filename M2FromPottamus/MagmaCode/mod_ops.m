/********** Some useful general Module functions ***********/

/*

   Annihilator(M) - returns the ideal that is the annihilator of the module
		given by the co-kernel of polynomial matrix M.
   bettiResolve(M) - computes appropriate sequences of row and column
		weights vs, us s.t. (acting by right multiplication)
		m*n matrix M gives a map of homogeneous modules:
		R(-us1)+R(-us2)+..+R(-usm) -> R(-vs1)+..+R(-vsn)
                ie from Module(R,[us1,..,usm]) to Module(R,[vs1,..,vsn])
   BettiRes(res,fw) - computes a matrix giving the betti table (in an appropriate
		form) of the free resolution res. fw is either 0 or an array
		giving the weights of the 1st (non-zero) module of res.
   NonMinimalBettiRes(res,fw,max_cond) - computes the betti table of the
		minimal free resolution of a module from res, a NON-MINIMAL one.
   bettiM(M) - returns the "betti numbers" of the homog. polynomial matrix M
   ResolutionWeights(res,n,fw) - if res is a free resolution with whose 1st
		(non-zero) module has weights fw, computes the weights of the 
		nth module of the resolution.
   LeftKernel/RightKernel(M) - returns a basis for the left/right kernel of
		the polynomial matrix M.
   LeftKernelW/RightKernelW(M, wts) - as above but with column/row weights
		specified for homogeneity. THESE ARE REDUNDANT!
   MinimiseRep(M,col_wts) - for a homogeneous reduced module M, replaces M with
                M1 where the #relations have been minimised. Returns M1.

   My(Minimal)FreeResolution & MyHomology - temporary test functions
   KoszulComplex(R) - returns the standard Koszul complex for k[x1,..xn]
   MyHilbertSeries/Polynomial(M) - computes the hilbert series or poly
		of a graded module
*/
Z := IntegerRing();
function Annihilator(M)
 // M is an r*s matrix in R giving a map from R^s to R^r.
 //  Function returns the annihilator of the cokernel.
 
 R := BaseRing(M);
 r := Nrows(M);
 s := Ncols(M);
 
 // do special cases first
 if r eq 1 then
    return ideal<R|Eltseq(M)>;
 end if;
 if s eq 1 then
    return &meet[ideal<R|m> : m in Eltseq(M)];
 end if;
  
 I := ideal<R|R!1>;
 F := Module(R,r-1);
 
 for i in [1..r] do
   modu := sub<F|[F!Eltseq(M1[j]) : j in [1..s]]>
	where M1 is Transpose(Matrix(R,[Eltseq(M[k]):k in [1..r] | k ne i]));
   syzs := [Eltseq(b) : b in Basis(SyzygyModule(modu))];
   I meet:= ideal<R | [ &+[row[j]*syz[j]:j in [1..s]] : syz in syzs]>
	where row is Eltseq(M[i]);
 end for;
 
 return I;
 
end function;

function bettiResolve(M)
// for an m*n matrix of homogeneous polynomials M, returns integer
// sequences vs,us of legths n,m s.t. degree(M[i,j])=us[i]-vs[j].
// If the vs and us don't exist or there are too many zero entries
// of M for vs,us to be uniquely determined, an error results.
    nr := Nrows(M); nc := Ncols(M);
    degs := Matrix(Integers(),nr,nc,[LeadingTotalDegree(f):f in Eltseq(M)]);

    _,i := Max([#[s:s in Eltseq(degs[j])|s ne -1]:j in [1..nr]]);
    vs := Eltseq(degs[i]);
    for j in [1..nc] do
	if vs[j] eq -1 then Undefine(~vs,j); end if;
    end for;

    while not ((#vs eq nc) and IsComplete(vs)) do
	i2 := [j:j in [1..nc]| IsDefined(vs,j)];
	i1 := [j: j in [1..nc]|j notin i2];
        j := 1;
        while j le nr do
	    pairs := [[u,v] : u in i1, v in i2 | (degs[j,u] ne -1) and
						   (degs[j,v] ne -1) ];
	    if #pairs ne 0 then
		u := pairs[1][1]; v := pairs[1][2];
		vs[u] := vs[v] + degs[j,v] - degs[j,u];
		break;
	    end if;
	    j +:= 1;
	end while;
	error if j gt nr, "Not enough matrix info to determine betti numbers"; 
    end while;

    us := [Integers()|];
    for j in [1..nr] do
	seq := [vs[k]+degs[j,k]:k in [1..nc]|degs[j,k] ne -1];
	error if #seq eq 0, "Not enough matrix info to determine betti numbers";
        error if #[s : s in seq| s ne seq[1]] gt 0, 
			"Matrix doesn't give homogeneous map";
	Append(~us,seq[1]);
    end for;

    return vs,us;

end function;

function bettiResolveRows(M,us)
// for an m*n matrix of homogeneous polynomials M, as in
// bettiResolve except that the us are already known and
// passed in as an argument.
    nr := Nrows(M); nc := Ncols(M);
    assert #us eq nr;

    vs := [Integers()|];
    for j in [1..nc] do Undefine(~vs,j); end for;

    for i in [1..nr], j in [1..nc] do
	deg := LeadingTotalDegree(M[i,j]);
	if deg ne -1 then
	    if IsDefined(vs,j) then
		error if deg ne (us[i]-vs[j]), "Input us are invalid";
	    else
		vs[j] := us[i]-deg;
	    end if;
	end if;
    end for;

    error if not ((#vs eq nc) and IsComplete(vs)), 
		"Not enough matrix info to determine betti numbers";
    return vs,us;

end function;

function bettiResolveCols(M,vs)
// for an m*n matrix of homogeneous polynomials M, as in
// bettiResolve except that the vs are already known and
// passed in as an argument.
    nr := Nrows(M); nc := Ncols(M);
    assert #vs eq nc;

    us := [Integers()|];
    for j in [1..nr] do Undefine(~us,j); end for;

    for i in [1..nr], j in [1..nc] do
	deg := LeadingTotalDegree(M[i,j]);
	if deg ne -1 then
	    if IsDefined(us,i) then
		error if deg ne (us[i]-vs[j]), "Input vs are invalid";
	    else
		us[i] := vs[j]+deg;
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

function mySubmat(M,rs,cs)
    M1 := Matrix([r[i] : i in rs]) where r is RowSequence(M);
    M2 := Matrix([r[i] : i in cs]) where r is RowSequence(Transpose(M1));
    return Transpose(M2);
end function;

function tidy_matrix(mat)
    if IsZero(mat) then return Matrix(Integers(),0,0,[]),0; end if;
    adj1 := 0;
    while IsZero(mat[1]) do
	mat := RowSubmatrix(mat,2,Nrows(mat)-1);
	adj1 +:= 1;
    end while;
    while IsZero(mat[Nrows(mat)]) do
	mat := RowSubmatrix(mat,Nrows(mat)-1);
    end while;
    nr := Nrows(mat);
    while &and[mat[i,Ncols(mat)] eq 0: i in [1..nr]] do
	mat := ColumnSubmatrix(mat,Ncols(mat)-1);
    end while;
    return mat,adj1;
end function;

procedure mat_rotate(~mat)
/* rotates the matrix by 180 degrees */
    mat := Matrix([Reverse(row) : row in Reverse(RowSequence(mat))]);
end procedure;

procedure easy_remove(~mat)
/* performs the reduction of type a) below on the betti matrix mat. 
   (and of type b) when called with mat = mat_rotate(betti matrix)  */
    col := 1; row := 1;
    b_spec := false;
    while row lt Nrows(mat) do
	col := Index(Eltseq(mat[row]),0,col);
	if col eq 0 then break; end if;
	for i in [col+1..Ncols(mat)] do
	    if mat[row,i] ne 0 then
		if mat[row+1,i-1] ge mat[row,i] then
		    mat[row+1,i-1] -:= mat[row,i];
		else //must remove entire block to the left of entry & adjust!
		    assert row eq 1;
		    for r in [1..Nrows(mat)-1] do
			diag := - &+[Integers()|((-1)^s)*mat[s+r,i-s] : 
				s in [1..Min(i-1,Nrows(mat)-r)]];
			assert (diag ge 0) and (diag le mat[r,i]);
			mat[r,i] -:= diag;
		    end for;
		    mat := ColumnSubmatrix(mat,i,Ncols(mat)-i+1);
		    b_spec := true; break;
		end if;
	    end if;
	end for;
	if b_spec then
	    b_spec := false;
	    col := 1;
	elif col eq 1 then
	    mat := RowSubmatrix(mat,2,Nrows(mat)-1);
	else
	    row +:= 1; 
	end if;
    end while;
    if col ne 0 then // check for final block of zeros in last row
	col := Index(Eltseq(mat[row]),0,col);
    end if;
    if col ne 0 then //remove final (zero) columns
	mat := ColumnSubmatrix(mat,col-1);
    end if;
end procedure;

function NonMinimalBettiRes(res,first_wts,max_cond)
// as above except that the given resolution is non-minimal.
// computes the betti table of the MINIMAL resolution without
// actually calculating it. Here first_wts must really give the
// first weights and not be 0.
// max_cond is a boolean that should be set to true if the
// condition that the sequence of maximal column weights in
// the minimal resolution is known to be strictly increasing
// (when "reduction b)" below can be applied).

    // first get all weights and build table
    Z := Integers();
    len := #BoundaryMaps(res)-1;
    all_wgts := [first_wts];
    vs := first_wts;
    for i in [1..len-1] do
	vs,us := bettiResolveCols(BoundaryMap(res,i),vs);
        vs := [u-1 : u in us];
        Append(~all_wgts,vs);
    end for;

    // build non-minimal betti table
    min,max := Explode([Min(seq),Max(seq)]) where seq is &cat all_wgts;
    mat := ZeroMatrix(Z,max-min+1,len);
    for i in [1..len], j in all_wgts[i] do
	mat[j-min+1,i] +:= 1;
    end for;

    // now look for "non-minimal" factors:
    //  these can come from diagonal lines in the betti table mat
    //  (eg mat[0,1],mat[1,0]) with consecutive non-zero entries.
    //  these are linked by constant submatrices of the transition 
    //  matrices of res. An entry on the diagonal is replaced by
    //   dim(ker M) - dim(im N) where M is the matrix going from it
    //   and N the one going to it.

    // for some non-minimal factors, the rank computations are
    //  unnecessary because we can deduce that the ranks are
    //  maximal are remove an entire betti table entry from mat.
    //  This is true because for the MINIMAL resolution
    //  a) the row index of the top non-zero entry in column i,
    //   of mat is a non-decreasing function of i.
    //  [b) below applies in certain cases - not entirely sure of
    //      all of them! - but in important cases like: res is the
    //      resolution of a finite (over the base field) or CM
    //      module. Although it is easy to construct examples
    //      when it fails, it seems to hold for most exs in practise]
    //  b) the row index of the bottom non-zero entry in column i,
    //   of mat is a non-decreasing function of i.
    //  a) & b) lead to reductions on the betti-matrix that
    //  are extra quick because they don't involve computing ranks
    //  of the constant transition matrices in res.
    //  [NB. b) gets rid of a lot of non-minmal entries in the common
    //   cases - eg the resolution of R/I for an ideal I whereas a)
    //   doesn't appear to perform any effective reduction on
    //   non-minimal resolutions coming from FreeResolution.]

    // do reductions by a)
    nr := Nrows(mat);
    easy_remove(~mat);
    min +:= (nr-Nrows(mat));

    // do reductions by b) if appropriate
    //  - use easy_remove on the betti-matrix "rotated by 180 degrees"
    if max_cond then
	mat_rotate(~mat);
	easy_remove(~mat);
	mat_rotate(~mat);
    end if;

    // now handle any other non-minimal factors that haven't been
    // dealt with by the above.
    nr := Nrows(mat); nc := Ncols(mat);
    K := BaseRing(BaseRing(Term(res,0)));
    for d in [3..nr+nc-1] do // d <-> (d-1)th diagonal
	dmax := Min(d-1,nr);
        // get maximal length chains of non-zero entries
        i := Max(1,d-nc);
        while i lt dmax do
          while (mat[i,d-i] eq 0) and (i lt dmax) do i +:= 1; end while;
          j := i+1;
          while (j le dmax) and (mat[j,d-j] ne 0) do j +:= 1; end while;
          if j gt i+1 then // chain with >= 2 elts
	    //get sequence of constant transition matrices for chain
	    // or rather their ranks (which is all that is needed!)
	    mat_rks := [0];
	    for k in [i..j-2] do
		M := BoundaryMap(res,d-k-1);
		rinds := [n : n in [1..#seq] | seq[n] eq min+k-1]  
		    where seq is all_wgts[d-k];
		cinds := [n : n in [1..#seq] | seq[n] eq min+k]  
		    where seq is all_wgts[d-k-1];
		M := ChangeRing(mySubmat(M,rinds,cinds),K);
		Append(~mat_rks,IsZero(M) select 0 else Rank(M));
	    end for;
	    Append(~mat_rks,0);
	    rks_sum := [mat_rks[k]+mat_rks[k+1]:k in [1..#mat_rks-1]];
	    for k in [k: k in [1..#rks_sum] | rks_sum[k] ne 0] do
		mat[i+k-1,d+1-i-k] -:= rks_sum[k];
	    end for; 
	  end if;
	  i := j;
	end while;
    end for;

    mat,adj1 := tidy_matrix(mat);
    min +:= adj1;

    return mat,min;

end function;

function ResolutionWeights(res,n,first_wts)
// Given a free resolution res whose zeroth term has col weights
//  first_wts, returns the col weights of the nth term of res. 
    assert (n ge 0) and (n lt #BoundaryMaps(res)-1);
    us := first_wts;
    for i in [1..n] do
	_,us := bettiResolveCols(BoundaryMap(res,i),us);
    end for;
    return us;
end function;

function bettiM(M)
// returns the "betti numbers" of the homogeneous polynomial matrix M
    return Matrix(Z,Nrows(M),Ncols(M),[TotalDegree(f):f in Eltseq(M)]);
end function;

function LeftKernel(M)
// returns a sequence of sequences, s,  s.t. the s give a
//  basis for the left kernel of polynomial matrix M
//  (seq s gives the coordinates of a kernel vector)
   Mmod := Module(BaseRing(M),Ncols(M));
   S := sub<Mmod|[M[i]:i in [1..Nrows(M)]]>;
   return [Eltseq(b): b in Basis(SyzygyModule(S))];
end function;

function LeftKernelW(M,wts)
// As above except that column weights wts are specified
//  s.t. the rows of M give homogeneous elements in the
// module R(-wts[1])+..+R(-wts[n]).
// NB. THIS FUNCTION IS ACTUALLY UNNECESSARY!
//  - The internal functions to compute the syzygys will
//  actually look for such weights and use them if they exist.
   Mmod := Module(BaseRing(M),wts);
   S := sub<Mmod|[M[i]:i in [1..Nrows(M)]]>;
   return [Eltseq(b): b in Basis(SyzygyModule(S))];
end function;

function RightKernel(M)
// returns a sequence of sequences, s,  s.t. the s give a
//  basis for the right kernel of polynomial matrix M
//  (seq s gives the coordinates of a kernel vector)
    return LeftKernel(Transpose(M));
end function;

function RightKernelW(M,wts)
// As above with wgts as for LeftKernelW in the transposed
//  situation and with the same comments applying.
    return LeftKernelW(Transpose(M),wts);
end function;

function MinimiseRep(M,col_wts)
    F := Module(BaseRing(M),col_wts);
    S := sub<F|[F!r : r in RowSequence(RelationMatrix(M))]>;
    B := MinimalBasis(S);
    M1 := quo<F1 | [F1!Eltseq(b) : b in B]> where 
		F1 is RModule(BaseRing(M),#col_wts);
    return M1;
end function;

function MyMinimise1(M)
/* 
   Takes a matrix M whose rows gives the relations for a module mod
   and returns a new matrix which give the relations wrt a minimal
   basis. [Temporary hack while core function is unavailable!]
   Also returns a  matrix giving the map from the
   minimal basis to the original basis.
   Actually should be able to use ReducedModule functions directly NOW!
*/
    tr := IdentityMatrix(BaseRing(M),Ncols(M));
    while true do
	ind := Index([TotalDegree(m) : m in Eltseq(M)],0);
        if ind eq 0 then break; end if; // M has no non-zero constant terms
        nc := Ncols(M); nr := Nrows(M);
	if nc eq 1 then return Matrix(BaseRing(M),0,0,[]); end if;
        row := Floor((ind-1)/nc) + 1;
	col := ind - (row-1)*nc;
	// M[row,col] is constant - eliminate variable col and 
	// adjust M accordingly
	MultiplyRow(~M,-1/M[row,col],row);
	for i in [1..nr] do
	    if i eq row then continue; end if;
	    AddRow(~M,M[i,col],row,i);
	end for;
	// remove row row and column col & adjust tr
	M := HorizontalJoin( ColumnSubmatrix(M,col-1),
		ColumnSubmatrix(M,col+1,nc-col) );
	tr *:= Matrix([rs[i]: i in [1..col-1]] cat [Eltseq(M[row])] cat
		[rs[i]: i in [col..nc-1]]) where rs is
		RowSequence(IdentityMatrix(BaseRing(M),nc-1));
	M := VerticalJoin(RowSubmatrix(M,row-1),RowSubmatrix(M,row+1,nr-row));
    end while;
    return M,Transpose(tr);	
end function;

function MyFreeResolution(md)
    assert Type(md) eq ModRngMPolRed;
    R := BaseRing(md);
    F0 := RModule(R,0);
    F := RModule(R,Degree(md));
    mps := [* RMatrixSpace(F,F0)!Matrix(R,Degree(F),0,[]) *];

    F1 := Module(R,Degree(md));
    rels := sub<F1|[F1!r : r in RowSequence(RelationMatrix(md))]>;
    while #Basis(rels) ne 0 do
	G := RModule(R,#Basis(rels));
	mat := Matrix(R,[Eltseq(b) : b in Basis(rels)]);
        mat := RMatrixSpace(G,F)!mat;
	F := G;
	Append(~mps,mat);
	rels := SyzygyModule(rels);
    end while;
    mps_rev := [* RMatrixSpace(F0,F)!Matrix(R,0,Degree(F),[]) *];
    for i := #mps to 1 by -1 do
	Append(~mps_rev,mps[i]);
    end for;
    return Complex(mps_rev,-1);
end function;

function MyMinimalFreeResolution(md,md_wts)
    assert ISA(Type(md), ModMPol);
    R := BaseRing(md);
    F0 := RModule(R,0);
    F := RModule(R,md_wts);//F := RModule(R,Degree(md));
    mps := [* Homomorphism(F,F0,Matrix(R,Degree(F),0,[])) *];

    wts := md_wts;
    F1 := Module(R,wts/*Degree(md)*/);
    rels := sub<F1|[F1!r : r in RowSequence(RelationMatrix(md))]>;
    B := MinimalBasis(rels);
    while #B ne 0 do
	// get new weights
	wts := [wts[i]+WeightedDegree(e[i]) where i is 
	   Min([i : i in [1..#e] | e[i] ne 0]) where e is Eltseq(b) : b in B];
	G := RModule(R,wts/*#B*/);
	mat := Matrix(R,[Eltseq(b) : b in B]);
        mat := Homomorphism(G,F,mat);
	F := G;
	Append(~mps,mat);
	rels := MinimalSyzygyModule(rels);
	B := MinimalBasis(rels);
    end while;
    mps_rev := [* Homomorphism(F0,F,Matrix(R,0,Degree(F),[])) *];
    for i := #mps to 1 by -1 do
	Append(~mps_rev,mps[i]);
    end for;
    return Complex(mps_rev,-1);
end function;

function MyHomology(res,i)
    F := Term(res,i);
    ker_mat := Matrix(BoundaryMap(res,i));
    im_mat := Matrix(BoundaryMap(res,i+1));

    R := BaseRing(F);
    F1 := Module(R,Degree(F));
    B := LeftKernel(Matrix([r: r in RowSequence(ker_mat)]));
    ke := sub<F1|[F1!b : b in B]>;
    Groebner(ke);
    incl := Matrix([Eltseq(b): b in Basis(ke)]);
    //construct homology module first non-minimally (on groebner basis of ke)
    rel_mat := Matrix([ChangeUniverse(Coordinates(ke,F1!r),R) : r in RowSequence(im_mat)] 
			cat [Eltseq(b) : b in Basis(SyzygyModule(ke))]);
    //minimise with inclusion map
    rel_mat,incl1 := MyMinimise1(rel_mat);
    F2 := RModule(R,Ncols(rel_mat));
    hm := Homomorphism(F2,F,incl1*incl);//RMatrixSpace(F2,F)!(incl1*incl);
    return quo<F2|[F2!r : r in RowSequence(rel_mat)]>,hm;
end function;

function KoszulComplex(R)
// Lazy implementation using MinFreeRes! Should do directly!
    I := ideal<R|[R.i : i in [1..Rank(R)]]>;
    Mk := QuotientModule(I);
    return MinimalFreeResolution(Mk);
end function;

function Omega_i(R,i)
// creates the twisted sheaf of order i differentials Omega^i(i)
// on Proj(R)
    kc := KoszulComplex(R);
    if i eq #Terms(kc)-4 then
	return Term(kc,#Terms(kc)-3);
    end if;
    mat := BoundaryMap(kc,i+2);
    N := Ncols(mat);
    F := RModule(R,N);
    return quo<F|[F!r : r in RowSequence(mat)]>,[1: j in [1..N]];
end function;

function ImageFromMat(mat,I)
// L is an invertible module on X <= P^(n-1) generated by global sections.
//  I is the defining ideal of X and
//  the module M_L = sum r>= 0 H^0(L(r)) has presentation matrix mat.
//
// Function returns the image of phi_L(X).

    n := Rank(I);
    m := Ncols(mat);

    // map is from P^n -> P^m - get it's graph from mat
    PG := PolynomialRing(BaseRing(I),n+m,"grevlex");
    incl_hom := hom<Generic(I) -> PG | [PG.i : i in [1..n]]>;
    I_gr := ideal<PG|[incl_hom(b) : b in Basis(I)] cat
	Eltseq(Matrix([[incl_hom(f) : f in r] : r in RowSequence(mat)])*
		Matrix(PG,m,1,[PG.(n+i): i in [1..m]])) >;

    // now get image of adjoint map by projecting to last m variables
    // by elimination
    P_gr := Generic(I_gr);
    // must saturate the ideal before projection. In this case
    // (the graph is an irreducible scheme), this only needs to be
    // done with one of the coordinate variables to be eliminated
print "Saturating..";
    I_gr_sat := ColonIdeal(I_gr,P_gr.1);
print "   Done";
//return I_gr_sat;

print "Eliminating..";
    //I_im := EliminationIdeal(I_gr_sat,n);
    GB := GroebnerBasis(I_gr_sat);
    B_im := [f : f in GB | &and[e[i] eq 0 : i in [1..n]] 
			where e is Exponents(LeadingTerm(f))];
print "   Done";
    Py<[y]> := PolynomialRing(BaseRing(I),m,"grevlex");
    Iy := ideal<Py|[hm(b) : b in B_im]> where
	hm is hom<P_gr->Py|[0: i in [1..n]] cat [Py.i : i in [1..m]]>;
    //Iy is the ideal of the image

    Xy := Scheme(Proj(Py),Iy); // image in P^m
    return Xy;

end function;

function MyHilbertSeries(M)
// computes the Hilbert series of graded module M (must be a 
// quotient module)

    assert Type(M) eq ModMPol;
    R := BaseRing(M);
    n := Ncols(M);
    if n eq 0 then return RationalFunctionField(Integers())!0; end if;
    rels := GroebnerBasis(sub<Universe(R) | R>) where 
		R is Relations(M);
    wts := ColumnWeights(M);
    
    lead_rels := [LeadingTerm(r) : r in rels];
    Iseq := [[]: i in [1..n]];
    for lr in lead_rels do
	j := 1;
	while (lr[j] eq R!0) and (j le n) do j +:= 1; end while;
	if j le n then Append(~(Iseq[j]),lr[j]); end if;
    end for;
    Is := [ideal<R|seq> : seq in Iseq];
    for I in Is do MarkGroebner(I); end for;

    // get hilb series for each ideal
    HSs := [HilbertSeries(I) : I in Is];
    // shift by col weights
    t := Parent(HSs[1]).1;
    HSs := [(t^wts[i])*HSs[i] : i in [1..n]];

    return &+HSs;

end function;

function MyHilbertPolynomial(M)
// computes the Hilbert polynomial of graded module M (must be a 
// quotient module) and minimal k s.t. H(d) agrees with the Hilbert
// function of I at d for d >= k.

    HS := MyHilbertSeries(M);
    den := Denominator(HS);
    num := Numerator(HS);
    if IsZero(num) then return num,0; end if;

    // deal with possible t in the denominator
    t := Parent(den).1;
    d := Min([i : i in [1..#cs] | cs[i] ne 0])-1 where
		cs is Coefficients(den);
    if d gt 0 then
	den div:= t^d;
	d := -d;
    end if;

    d +:= Max(0,Degree(num)-Degree(den)+1);
    dd := Degree(den);
    num := (num mod den);
    num1 := Evaluate(num,t+1);
    assert Evaluate(den,t+1) eq t^dd;
    cs := Coefficients(num1);
    cs cat:= [0 : i in [1..dd-#cs]];
    
    // HilbPoly(x) is sum_i (-1)^(dd+1-i)*cs[i]*Binomial(x+dd-i,dd-i)
    R := PolynomialRing(Rationals());
    x := R.1; HP := R!(cs[1]);
    for i in [1..dd-1] do
	HP := HP*((x+(dd-i))/(dd-i)) - R!(cs[i+1]);
    end for;

    return ((-1)^dd)*HP,d;

end function;
