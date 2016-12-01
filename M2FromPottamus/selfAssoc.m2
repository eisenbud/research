--This file contains 

--selfAssoc 
--(tests a finite projective scheme for self-association

--selfAssoc1 
--(same but for scheme given as art ring and vector space)

--multTable 
--(computes the mult table of a fin dim alg)

-------------------------------------
selfAssoc = Q ->(
     u := ideal(1-(vars Q) * 
       random(source vars Q,
       Q^{-1}));
     Qbar := Q/u;
     selfAssoc1 (Qbar,(vars Q)**Qbar)
     )

document {quote selfAssoc,
         TT "-- selfAssoc(Q: homogeneous coordinate ring of finite scheme)",BR,
NOINDENT,"Given the homogeneous coordinate ring
of a finite scheme in projective space,
this function returns TRUE
if the scheme is self-associated.
We first reduce mod a generic linear form, then call 
selfAssoc1
to deal with the inhomogeneous case. See the 
documentation of selfAssoc1 for more information.
CAVEATS: The linear form must not vanish
on the scheme; if the field is too small this
could be a problem. Could probably do it a little
faster by replacing one of the variables by 1
in the matrix representing the linear forms.
Also, if one of the variables does not vanish
at any point of x, using it as the linear form
would probably make the computation faster.",PARA,
EXAMPLE 
///
-- the set consisting of 4 points on each of 
-- two skew lines in P3 is self-associated
kk=ZZ/101
R=kk[a,b,c,d]
I= saturate (intersect(ideal(a,b),
     ideal(c,d))+
     ideal((a+c)^4))
selfAssoc (R/I)
         ///,
EXAMPLE 
///
-- While  4 points on one and three points on the other
--is not.
kk=ZZ/101
R=kk[a,b,c,d]
use R
I=intersect(
     ideal(a,b,c),
     ideal(a,b,d),
     ideal(a,b,c+d),
     ideal(a,b,c-d),
     ideal(c,d,a),
     ideal(c,d,b),
     ideal(c,d,a+b) --,ideal(c,d,a-7*b)
     )
degree I
selfAssoc (R/I)
         ///,
"   Created by DE, 8/19/98."
	}
eg1=()->(
     kk:=ZZ/101;
     R:=kk[a,b,c,d];
     I:= saturate (intersect(ideal(a,b),
     ideal(c,d))+
     ideal((a+c)^4));
     selfAssoc (R/I)
         )
eg2=()->(
     kk:=ZZ/101;
     R:=kk[a,b,c,d];
     I:=intersect(
     ideal(a,b,c),
     ideal(a,b,d),
     ideal(a,b,c+d),
     ideal(a,b,c-d),
     ideal(c,d,a),
     ideal(c,d,b),
     ideal(c,d,a+b) --,ideal(c,d,a-7*b)
     );
     selfAssoc (R/I)
         )

------------------------------------------------

selfAssoc1 = (Q,V)->(
     B := (basis Q)**Q;
     n := rank source B;
     k := coefficientRing Q;
     S := k[A_0..A_(n-1)];
     G := S^n;
     -- Make the multiplication table, over Q
     use ring B;
     m1 := 1*(B**B);
     -- and the row of elements of V*V
     vv1 := 1*(V**V);
     -- (the operation ** does not
     -- automatically reduce its entries;
     -- mult by 1 corrects this.)
     --
     -- The columns of m2 are the coefficients
     -- of the elements of the row matrix m1 in terms of the
     -- basis B
     m2 := transpose substitute(contract(transpose m1,B),0);
     m2 = lift(m2,k);
     -- m3 is the same, expressed as a row matrix of linear forms
     m3 := (vars S)*m2;
     -- and finally the table
     m := adjoint(m3,G,G);
     -- Now do the same for VV
     vv2 := transpose substitute(contract(transpose vv1,B),0);
     vv2 = lift(vv2,k);
     vv := (vars S)*vv2;
     mbar := m**(S/ideal(vv));
     (kernel mbar)==0
          )

document {quote selfAssoc1,
         TT "-- selfAssoc1(Q: Finite dimensional algebra, V: Row
--matrix representing the subspace of linear forms)",BR,
NOINDENT,"Given a finite scheme in projective space
represented by a FINITE DIMENSIONAL algebra Q, 
and a row matrix giving generators for the 
subspace of linear forms,
this function returns TRUE
if the finite scheme is self-associated.
The idea is to form the multiplication table of Q 
as a matrix of linear forms over a new polynomial ring 
S = Sym Q
whose variables correspond to a basis of Q.
We then tensor the matrix with S/(VV),
where VV is the space of linear forms in S
coming from the subspace V*V of Q. This reduction
represents the generic pairing on Q that annihilates
VV. Self-association means that it becomes an isomorphism
on generic specialization to a symmetric matrix over
the ground field, that is, if its rank is equal to
the dimension of Q.",PARA,
EXAMPLE 
///
-- the set consisting of 4 points on each of 
-- two skew lines in P3 is self-associated
kk=ZZ/101
R=kk[a,b,c,d]
I= saturate (intersect(ideal(a,b),
     ideal(c,d))+
     ideal((a+c)^4))
degree I
dim I
x=(vars R) * 
       random(source vars R, 
       R^{-1})
Q=R/(I+ideal(x-1))
V=matrix{{1,b,c,d}}
selfAssoc1 (Q,V)
         ///,
EXAMPLE 
///
-- While  4 points on one and three points on the other
--is not.
kk=ZZ/101
R=kk[a,b,c,d]
use R
I=intersect(
     ideal(a,b,c),
     ideal(a,b,d),
     ideal(a,b,c+d),
     ideal(a,b,c-d),
     ideal(c,d,a),
     ideal(c,d,b),
     ideal(c,d,a+b) --,ideal(c,d,a-7*b)
     )
degree I
x=(vars R) * 
       random(source vars R, 
       R^{-1})
Q=R/(I+ideal(x-1))
V=matrix{{1,b,c,d}}
load "multTable.m2"
selfAssoc1 (Q,V)
         ///,
"   Created by DE, 8/19/98."
	}

egi1=()->(
kk=ZZ/101;
R=kk[a,b,c,d];
I= saturate (intersect(ideal(a,b),
     ideal(c,d))+
     ideal((a+c)^4));
x=(vars R) * 
       random(source vars R, 
       R^{-1});
Q=R/(I+ideal(x-1));
V=matrix{{1,b,c,d}};
selfAssoc1 (Q,V)
   )

---------------------------------------
multTable = (Q)->(
     B := (basis Q)**Q;
     n := rank source B;
     k := coefficientRing Q;
     S := k[A_0..A_(n-1)];
     G := S^n;
     -- Make the multiplication table, over Q
     m1 := 1*(B**B);
     -- the operation ** does not
     -- automatically reduce its entries;
     -- mult by 1 corrects this.
     --
     -- The columns of m2 are the coefficients
     -- of the elements of the row matrix m1 in terms of the
     -- basis B
     m2 := transpose substitute(contract(transpose m1,B),0);
     m2 = lift(m2,k);
     -- m3 is the same, expressed as a row matrix of linear forms
     m3 := (vars S)*m2;
     -- and finally the table
     adjoint(m3,G,G)
     )

document {quote multTable,
         TT "-- multTable(Q: Finite dimensional algebra)",BR,
NOINDENT,
"Given a FINITE DIMENSIONAL algebra Q, 
this function returns the multiplication table of Q 
as a matrix of linear forms over a new polynomial ring 
S = Sym Q
whose variables correspond to a basis of Q.
The table is thus a map
S**Q-->S**Q^*(1).",PARA,
EXAMPLE 
///
-- The affine algebra of 4 points on each of 
-- two skew lines in P3
--restart
kk=ZZ/101
R=kk[a,b,c,d]
I= saturate (intersect(ideal(a,b),
     ideal(c,d))+
     ideal((a+c)^4))
x=(vars R) * 
       random(source vars R, 
       R^{-1})
Q=R/(I+ideal(x-1))
dim Q
multTable Q
         ///,
"   Created by DE+DG, 8/19/98."
	}





