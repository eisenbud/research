
--- 5/8/2016

--Polar-Homogenization


oneVarHomogenize = method()
oneVarHomogenize(Ideal,RingElement,ZZ) := (I,x,i) -> (
    R := ring I;
    V := flatten entries vars R;
    n := length V;
    D := flatten degrees R;
    if not isPolynomialRing R then error "Expected first argument to be an ideal over a polynomial ring";
    if not (ring x === R) then error "Expected second argument to be an element of the ring of the given ideal";
    if not (any(V,l->l==x)) then error "Expected second argument to be a variable in the ring of the given ideal";
    if not isHomogeneous I then error "Expected first argument to be a homogeneous ideal";
    d := first degree x;
    if d == 1 then return I;
    K := coefficientRing R;
    j := -1;
    for i from 0 to n - 1 do( if x == V_i then j = i );
    v = symbol X_i;
    newD := append(for i from 0 to n - 1 list(
	if i == j then 1 else D_i),1);
    newV := append(V,v);
    S := K[newV,Degrees=>newD];
    actualNewV := flatten entries vars S;
    L := for i from 0 to length V - 1 list(
	if i == j then actualNewV_i*actualNewV_n^(d-1) else actualNewV_i);
    f := map(S,R,L);
    return f(I);
    )

oneVarHomogenize2 = method()
oneVarHomogenize2(Ideal,RingElement,ZZ) := (I,x,i) -> (
    R := ring I;
    V := flatten entries vars R;
    n := length V;
    D := flatten degrees R;
    if not isPolynomialRing R then error "Expected first argument to be an ideal over a polynomial ring";
    if not (ring x === R) then error "Expected second argument to be an element of the ring of the given ideal";
    if not (any(V,l->l==x)) then error "Expected second argument to be a variable in the ring of the given ideal";
    if not isHomogeneous I then error "Expected first argument to be a homogeneous ideal";
    d := first degree x;
    if d == 1 then return I;
    K := coefficientRing R;
    j := -1;
    for i from 0 to n - 1 do( if x == V_i then j = i );
    v := symbol X_i;
    newD = append(for i from 0 to n - 1 list(
	if i == j then 1 else D_i),1);
    newV := append(V,v);
    S := K[newV,Degrees=>newD];
    actualNewV := flatten entries vars S;
    L := for i from 0 to length V - 1 list(
	if i == j then actualNewV_i else actualNewV_i);
    f := map(S,R,L);
    return homogenize(f(I),last flatten entries vars S);
    )


polarHomogenize = method()
polarHomogenize(Ideal) := (I) -> (
    R := ring I;
    V := flatten entries vars R;
    n := length V;
    D := flatten degrees R;
    J := I;
    k := 1;
    for i from 1 to n do(
    	    S := ring J;
	    W := flatten entries vars S;
	    J = oneVarHomogenize(J,W_(i-1),i);
    	    k = k + 1;
    );
    return J;
    )

polarHomogenize2 = method()
polarHomogenize2(Ideal) := (I) -> (
    R := ring I;
    V := flatten entries vars R;
    n := length V;
    D := flatten degrees R;
    J := I;
    k := 1;
    for i from 1 to n do(
    	    S := ring J;
	    W := flatten entries vars S;
	    J = oneVarHomogenize2(J,W_(i-1),i);
    );
    return J;
    )


-- Rees-Like Algebra

reesPrime2 = method()
reesPrime2(Ideal) := (I) -> (
    R := ring I;
    V := flatten entries vars R;
    n := length V;
    D := flatten degrees R;
    K := coefficientRing R;
    if not isField K then error "Expected an ideal in a polynomial ring over a field";
    if not isPolynomialRing R then error "Expected an ideal in a polynomial ring over a field";
    if not isHomogeneous I then error "Expected a homogeneous ideal";
    W := for i from 1 to length V list symbol w_i;
    t := symbol t;
    T := K[W,t];
    f := map(T,R,remove(flatten entries vars T,n));
    J := f(I);
    G := flatten entries mingens J;
    m := length G;
    Ylist := for i from 1 to length G list symbol Y_i;
    Xlist := for i from 1 to n list symbol x_i;
    z := symbol Z;
    DYlist := for i from 1 to length G list first degree G_(i-1) + 1;
    DXlist := for i from 1 to n list 1;
    deglist := {2} | DYlist  | DXlist;   
    L := {t^2} | apply(G,v->v*t) | remove(flatten entries vars T,n);
    S := K[z,Ylist,Xlist,Degrees=>deglist,MonomialOrder=>Lex];
    phi := map(T,S,L);
    return ker phi
    )

reesPrime = method()
reesPrime(Ideal) := (I) -> (
    R := ring I;
    V := flatten entries vars R;
    n := length V;
    D := flatten degrees R;
    K := coefficientRing R;
    if not isField K then error "Expected an ideal in a polynomial ring over a field";
    if not isPolynomialRing R then error "Expected an ideal in a polynomial ring over a field";
    if not isHomogeneous I then error "Expected a homogeneous ideal";
    W := for i from 1 to length V list symbol w_i;
    T := K[W,t];
    f := map(T,R,remove(flatten entries vars T,n));
    J := f(I);
    G := flatten entries mingens J;
    m := length G;
    Ylist := for i from 1 to length G list symbol Y_i;
    Xlist := for i from 1 to n list symbol x_i;
    DYlist := for i from 1 to length G list first degree G_(i-1) + 1;
    DXlist := for i from 1 to n list 1;
    deglist := DYlist  | DXlist;   
    L := apply(G,v->v*t) | remove(flatten entries vars T,n);
    S := K[Ylist,Xlist,Degrees=>deglist,MonomialOrder=>Lex];
    phi := map(T,S,L);
    return ker phi
    )

-- FIX ME!!!  I NEED MORE T VARIABLES!!!
reesModulePrime = method()
reesModulePrime(Module) := (M) -> (
    R := ring M;
    V := flatten entries vars R;
    n := length V;
    D := flatten degrees R;
    K := coefficientRing R;
    if not isField K then error "Expected a module in a polynomial ring over a field";
    if not isPolynomialRing R then error "Expected a module in a polynomial ring over a field";
    if not isHomogeneous M then error "Expected a homogeneous module";
    W := for i from 1 to length V list symbol w_i;
    T := K[W,t];
    f := map(T,R,remove(flatten entries vars T,n));
    N := f(presentation(M));
    G := flatten entries mingens J;
    m := numcols N;
    Ylist := for i from 1 to length  list symbol Y_i;
    Xlist := for i from 1 to n list symbol x_i;
    z := symbol Z;
    DYlist := for i from 1 to length G list first degree G_(i-1) + 1;
    DXlist := for i from 1 to n list 1;
    deglist := DYlist | {2} | DXlist;   
    L := append(apply(G,v->v*t),t^2) | remove(flatten entries vars T,n);
    S := K[Ylist,z,Xlist,Degrees=>deglist];
    phi := map(T,S,L);
    return ker phi
    )


