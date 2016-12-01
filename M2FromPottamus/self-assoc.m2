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
x-1
Q=R/(I+ideal(x-1))
dim Q
B=basis Q
(B**Q)_(0,0)
mtable=map(Q^8,Q^8,(i,j)->
     ((B**Q)_(0,i))*((B**Q)_(0,j)))
coefficients mtable_(3,1)

entries mtable

--wish list
transpose B
B**B
c^2//B

betti res I

J=intersect(
     ideal(a,b,c),
     ideal(a,b,d),
     ideal(a,b,c+d),
     ideal(a,b,c-d),
     ideal(c,d,a),
     ideal(c,d,b),
     ideal(c,d,a+b),
     ideal(c,d,a-7*b))
betti res J
--So resolution type
--
--    total: 1 6 8 3
--      0: 1 . . .
--      1: . 4 4 1
--      2: . . . .
--      3: . 2 4 2
--
--does not depend on the cross
--ratios on the two lines!

---------------------
n=rank source vars R
vars R
(vars R)_{n-1}

multTable = (Q)->(
     -- given a FINITE DIMENSIONAL algebra
     -- Q, produces the mult table of 
     -- Q as a matrix of linear
     -- forms over a new poly ring 
     -- S = Sym Q
     -- whose variables correspond to 
     -- to elements of the module. 
     -- The table is thus a map
     -- S**Q-->S**Q^*(1).
     -- Eisenbud+Grayson 8/19/98
     B=(basis Q)**Q;
     n:=degree Q;
     kk:=coefficientRing Q;
     S=kk[A_0..A_{n-1}];
     G=S^n;
     m1= 1*(B**B);
     -- the operation ** does not
     -- automatically reduce its entries;
     -- mult by 1 corrects this.
     m2 = lift transpose substitute(contract(transpose m1,B),0);
     m3 = (vars S)*m2;
     adjoint(m3,G,G)
     )
     



isAssoc=(I)->(
     n=(rank source vars ring I);
--choose a 1x1 matrix whose entry is a 
--nzd mod I
     x=(vars R)_{n-1};
     if ker(x**(R^1/I)) != 0 then
	  x=(vars R) * 
	  random(source vars R, 
	       R^{-1});
--pass to R/x-1
     Q=R/(I+ideal(x-1))
     basis Q
--form the multiplication table
--as a matrix over Q
mtable=map(Q^8,Q^8,(i,j)->
     ((B**Q)_(0,i))*((B**Q)_(0,j)))
      )
(entries mtable_0
contract(B,(entries mtable)_0)
help contract

isAssoc I






