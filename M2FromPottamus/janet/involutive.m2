-- methods for Janet bases and Pommaret bases
-- for Macaulay 2, version 0.9.95
-- last modification: Sep 28 2007


----------------------------------------------------------------------
-- subroutines
----------------------------------------------------------------------

-- determine multiplicative variables for list of
-- exponents exp2 with respect to Janet division
-- (exp1 is list of exponents of monomial which is
-- lexicographically next greater than that with exp2,
-- and has multiplicative variables indicated by mult1)
janetDivision = (exp1, exp2, mult1) -> (
     n := length(exp1);
     k := 0;
     mult2 := {};
     while (k < n and exp1#k == exp2#k) do (
	  mult2 = append(mult2, mult1#k);
	  k = k+1;
     );
     if k == n then error "list of polynomials is not autoreduced";
     mult2 = append(mult2, 0);
     k = k+1;
     while k < n do (
	  mult2 = append(mult2, 1);
	  k = k+1;
     );
     return mult2;
     )

-- determine multiplicative variables for list of
-- exponents exp2 with respect to Pommaret division
pommaretDivision = (expon) -> (
     n := length(expon);
     k := n-1;
     mult := {};
     while (k >= 0 and expon#k == 0) do (
	  mult = prepend(1, mult);
	  k = k-1;
     );
     if k >= 0 then ( mult = prepend(1, mult); k = k-1; );
     while k >= 0 do (
	  mult = prepend(0, mult);
	  k = k-1;
     );
     return mult;
     )

-- decide whether list of exponents exp1 (with multiplicative
-- variables given by mult1) is an involutive divisor of exp2
involutiveDivisor = (exp1, exp2, mult1) -> (
     for i from 0 to length(exp1)-1 do (
	  if (exp1#i > exp2#i or (exp1#i < exp2#i and mult1#i == 0)) then return false;
     );
     return true;
     )

-- given a list L of (leading) monomials, return list of their
-- multiplicative variables with respect to Janet division
janetMultVarMonomials = L -> (
     R := ring L#0;
     F := coefficientRing R;
     v := generators R;
     n := length v;
     S := F[v, MonomialOrder=>Lex];
     M := matrix { for i in L list substitute(i, S) };
     p := reverse sortColumns M;
     mult := for i in v list 1;
     J := { hashTable(for j from 0 to n-1 list v#j => mult#j) } |
          for i from 1 to length(L)-1 list (
	       mult = janetDivision(
		    (exponents (entries M_(p#(i-1)))#0)#0,
		    (exponents (entries M_(p#i))#0)#0,
		    mult);
	       hashTable(for j from 0 to n-1 list v#j => mult#j)
	       );
     p = for i from 0 to length(p)-1 list position(p, j -> j==i);
     return for i from 0 to length(p)-1 list J#(p#i);
     )

-- given a monomial m in a polynomial ring with n variables,
-- return the class of m
monomialClass = (m, n) -> (
     expon := (exponents m)#0;
     k := n-1;
     while (k >= 0 and expon#k == 0) do ( k = k-1; );
     return k;
     )

-- subroutine used by invResolution,
-- sorts Janet basis such that iterated syzygy computation is
-- possible (schreyerOrder depends on this order of the Janet basis)
sortByClass = (J, mult) -> (
     R := ring J;
     v := generators R;
     n := length v;
     L := leadTerm J;
     L = for i from 0 to (numgens source L)-1 list
          { leadMonomial sum entries L_i, leadComponent L_i };
     p := toList(0..(length(mult)-1));
     F := coefficientRing R;
     S := F[v, MonomialOrder=>Lex];
     modified := true;
     while modified do (
	  modified = false;
	  for i from 1 to length(p)-1 do
	       if (L#(p#i)#1 < L#(p#(i-1))#1 or (L#(p#i)#1 == L#(p#(i-1))#1 and
		  (monomialClass(L#(p#i)#0, n) < monomialClass(L#(p#(i-1))#0, n) or
		  (monomialClass(L#(p#i)#0, n) == monomialClass(L#(p#(i-1))#0, n) and
		   substitute(L#(p#i)#0, S) > substitute(L#(p#(i-1))#0, S))))) then (
	          p = for j from 0 to length(p)-1 list (
		       if j == i-1 then
		          p#i
		       else if j == i then
		          p#(i-1)
		       else
		          p#j
	          );
	          modified = true;
	       );
     );
     return (submatrix(J, p), for i from 0 to length(p)-1 list mult#(p#i));
     )


----------------------------------------------------------------------
-- main routines (work for ideals and more generally for submodules)
----------------------------------------------------------------------

-- given a matrix M of polynomials, return the list of
-- multiplicative variables for each column with respect to
-- Janet division
janetMultVar = M -> (
     R := ring M;
     F := coefficientRing R;
     v := generators R;
     n := length v;
     S := F[v, MonomialOrder=>{Position=>Up, Lex}];
     L := substitute(leadTerm M, S);
     p := reverse sortColumns L;
     J := for i from 0 to length(p)-1 list
          { leadMonomial sum entries L_(p#i), leadComponent L_(p#i) };
     -- select generators according to their leading component
     J = for i from 0 to (numgens target M)-1 list
	  select(J, j -> j#1 == i);
     local mult;
     J = flatten for k from 0 to (numgens target M)-1 list (
          mult = for i in v list 1;
          { hashTable(for j from 0 to n-1 list v#j => mult#j) } |
          for i from 1 to length(J#k)-1 list (
	       mult = janetDivision(
		    (exponents J#k#(i-1)#0)#0,
		    (exponents J#k#i#0)#0,
		    mult);
	       hashTable(for j from 0 to n-1 list v#j => mult#j)
	       )
	  );
     p = for i from 0 to length(p)-1 list position(p, j -> j==i);
     use R;
     return for i from 0 to length(p)-1 list J#(p#i);
     )

-- given a matrix M of polynomials, return the list of
-- multiplicative variables for each column with respect to
-- Pommaret division
pommaretMultVar = M -> (
     v := generators ring M;
     n := length v;
     local mult;
     return for i from 0 to (numgens source M)-1 list (
	  mult = pommaretDivision((exponents leadMonomial sum entries leadTerm M_i)#0);
          hashTable(for j from 0 to n-1 list v#j => mult#j)
          );
     )

-- given a (minimal) Groebner basis G for a submodule of a
-- free module over a polynomial ring, return a (minimal)
-- Janet basis for the same submodule
-- (up to now, it is not tail-reduced),
-- that is a pair (matrix, list of hash tables of mult. var.)
janetBasis = G -> (
     M := generators G;
     R := ring M;
     v := generators R;
     M = for i from 0 to (numgens target M)-1 list
          submatrix(M, select(toList(0..(numgens source M)-1),
		    j -> leadComponent leadTerm M_j == i));
     local J;
     local N;
     local P;
     local Q;
     M = for c from 0 to length(M)-1 list (
	  N = M#c;
	  if numgens source N == 0 then continue;
	  -- leading monomials are all in c-th row
	  J = janetMultVarMonomials for i in flatten entries N^{c} list leadMonomial i;
	  P = flatten for i from 0 to length(J)-1 list (
	       for j in v list (
		    if J#i#j == 1 then continue;
		    j * N_{i}
		    )
	       );
	  P = for i in P list (
	       if length(select(toList(0..length(J)-1),
		    j -> involutiveDivisor(
		    (exponents leadMonomial (entries N^{c}_j)#0)#0,
		    (exponents leadMonomial (entries i^{c})#0#0)#0,
		    for k in v list J#j#k))) > 0 then continue;
	       i
	       );
	  while length(P) > 0 do (
	       Q = P#0;
	       for i from 1 to length(P)-1 do Q = Q | P#i;
	       N = N | matrix { (sort Q)_0 };
	       J = janetMultVarMonomials for i in flatten entries N^{c} list leadMonomial i;
	       P = flatten for i from 0 to length(J)-1 list (
		    for j in v list (
			 if J#i#j == 1 then continue;
			 j * N_{i}
			 )
		    );
	       P = for i in P list (
		    if length(select(toList(0..length(J)-1),
			 j -> involutiveDivisor(
			 (exponents leadMonomial (entries N^{c}_j)#0)#0,
			 (exponents leadMonomial (entries i^{c})#0#0)#0,
			 for k in v list J#j#k))) > 0 then continue;
		    i
		    );
	  );
          (N, J)
     );
     p := sortColumns M#0#0;
     P = submatrix(M#0#0, p);
     J = for j from 0 to length(p)-1 list M#0#1#(p#j);
     for i from 1 to length(M)-1 do (
	  p = sortColumns M#i#0;
	  P = P | submatrix(M#i#0, p);
	  J = J | for j from 0 to length(p)-1 list M#i#1#(p#j);
     );
     return (P, J);
     )

-- given a Janet basis J for a submodule of a free module
-- over a polynomial ring, as returned by janetBasis, decide
-- whether it is also a Pommaret basis for the same module
isPommaretBasis = J -> (
     v := generators ring J#0;
     P := pommaretMultVar J#0;
     for i from 0 to length(J#1)-1 do (
	  for j in v do (
	       if J#1#i#j != P#i#j then return false;
          );
     );
     return true;
     )

-- given a Janet basis (J, mult) for a submodule of a free module
-- over a polynomial ring and an element p of this free module,
-- return the normal form of p modulo J and the coefficients
-- used for involutive reduction
invReduce = (p, J) -> (
     R := ring J#0;
     v := generators R;
     L := leadTerm J#0;
     L = for i from 0 to (numgens source L)-1 list
          { leadMonomial sum entries L_i,
	    leadComponent L_i,
	    leadCoefficient sum entries L_i };
     zl := 0*(target p)_0;
     zr := 0*(R^(length L))_0;
     local i;
     local c;
     local f;
     local lc;
     local lm;
     local lt;
     local m;
     local q;
     local r;
     L = for j from 0 to (numgens source p)-1 list (
	  q = p_j;
	  r = zl;
	  c = zr;
	  f = (v#0)^0;  -- equals 1
	  while matrix {q} != 0 do (
	       lt = leadTerm q;
	       m = leadComponent lt;
	       lc = leadCoefficient sum flatten entries lt;
	       lm = leadMonomial sum flatten entries lt;
	       i = 0;
	       while i < length(L) do (
		    if (m == L#i#1) and involutiveDivisor(
			 (exponents L#i#0)#0,
			 (exponents lm)#0,
			 for k in v list J#1#i#k) then break;
		    i = i + 1;
	       );
	       if i < length(L) then (
		    q = L#i#2 * q - lc * (lm // L#i#0) * J#0_i;
		    c = c + lc * (lm // L#i#0) * (R^(length L))_i;
		    r = L#i#2 * r;
		    f = L#i#2 * f;
	       )
	       else (
		    q = q - lt;
		    r = r + lt;
	       );
	  );
          r = apply(r, i -> i // f);
          c = apply(c, i -> i // f);
          (r, c)
     );
     N := matrix { L#0#0 };
     C := matrix { L#0#1 };
     for j from 1 to length(L)-1 do (
	  N = N | matrix { L#j#0 };
	  C = C | matrix { L#j#1 };
     );
     return (N, C);
     )

-- given a Janet basis (J, mult) for a submodule of a free module
-- over a polynomial ring, as returned by janetBasis, return
-- Janet basis for the syzygies of J;
-- cannot be iterated because schreyerOrder is not used
invSyzygies = (J, mult) -> (
     R := ring J;
     v := generators R;
     zl := 0*(target J)_0;
     local r;
     S := flatten for i from 0 to (numgens source J)-1 list (
	  for j in v list (
	       if mult#i#j == 1 then continue;
               r = invReduce(j * J_{i}, (J, mult));
	       if (r#0)_0 != zl then error "given data is not a Janet basis";
	       r = matrix { j * (R^(length(mult)))_i } - r#1;
	       (r, hashTable(for k in v list if k <= j then ( k => 1 ) else ( k => mult#i#k )))
	  )
     );
     if length(S) > 0 then (
	  M := S#0#0;
	  L := { S#0#1 };
	  for j from 1 to length(S)-1 do (
	       M = M | S#j#0;
	       L = L | { S#j#1 };
	  );
	  return (M, L);
     )
     else (
	  return ( matrix(R, apply(length(mult), i -> {})), {} );
     );
     )

-- given a Janet basis (J, mult) for a submodule of a free module
-- over a polynomial ring, as returned by janetBasis, construct
-- a free resolution for this module
invResolution = (J, mult) -> (
     R := { sortByClass(J, mult) };
     S := invSyzygies R#(-1);
     S = (map(source schreyerOrder R#(-1)#0, source S#0, S#0), S#1);
     while length(S#1) > 0 do (
	  R = R | { sortByClass(S) };
	  S = invSyzygies R#(-1);
          S = (map(source schreyerOrder R#(-1)#0, source S#0, S#0), S#1);
     );
     return R;
     )
