load "noetherianOperatorsCode.m2"
 
----------------------------------------------------
-- SEVERAL EXAMPLES -----------------------------------
----------------------------------------------------


----------------------------------------------------
----------------------------------------------------
-- Example 1: first a monomial example
R = QQ[x1, x2]
I = ideal(x1^3, x1^2*x2^2)
L = solvePDE(I) -- compute our notion of diffPrimDec
    	     -- the number of Noetherian ops is 4
I' = getPDE L	     
I == I' -- check the ideals are equal
amult(I) -- compute the arithmetic multiplicity
sum apply(primaryDecomposition I, Q -> amult Q) -- compute the multiplicity of the primary components
    	    	-- this is the "naive number" of Noetherian operators
----------------------------------------------------
----------------------------------------------------


----------------------------------------------------
----------------------------------------------------
-- Example 2: Example 13 of "Primary Ideals and 
--     Their Differential Equations" with k = 2
R = QQ[x1,x2,x3,x4]
k = 2
I = ideal((x1^2-x2*x3)^k,(x1*x2-x3*x4)^k,(x2^2-x1*x4)^k)
L = solvePDE I
I' = getPDE L
I == I' 
amult(I)
sum apply(primaryDecomposition I, Q -> amult Q)
--    If we do the naive encoding of Noetherian operators then we 
--    obtain 104 Noetherian operators. But, here we see that we ONLY 
--    amult(I) = 10 NOETHERIAN OPERATORS IS ENOUGH!!!! 
----------------------------------------------------
----------------------------------------------------


----------------------------------------------------
----------------------------------------------------
-- Example 3: Example 13 of "Primary Ideals and 
--     Their Differential Equations" with k = 3
R = QQ[x1,x2,x3,x4];
k = 3
I = ideal((x1^2-x2*x3)^k,(x1*x2-x3*x4)^k,(x2^2-x1*x4)^k);
L = solvePDE I
I' = getPDE L
I == I'
amult(I)
sum apply(primaryDecomposition I, Q -> amult Q)
-- The naive number of Noetherian operators is: 487. 
-- But, amult(I) = 29.
----------------------------------------------------
----------------------------------------------------




----------------------------------------------------
----------------------------------------------------
-- Example 4: An example constructed by hand
R = QQ[x1,x2,x3]
I = intersect(
    ideal(x1^4), 
    ideal(x1, x2^3*x1 + x3^5), 
    ideal(x1^2,x2^2,x3^3), 
    ideal(x2^3 + x1*x2*x3, x2^2 + x1^2*x3^3*x1)
    )
L = solvePDE I
I' = getPDE L
I == I' -- check the ideals are equal
amult(I)
sum apply(primaryDecomposition I, Q -> amult Q)
----------------------------------------------------
----------------------------------------------------


----------------------------------------------------
----------------------------------------------------
-- Example 5: Example 5.1 of Diaconis, Eisenbud and Sturmfels
--  treated in example in Example 5.5 of our paper
R = QQ[A,B,C,D] -- change the name of vars because "dd" cannont be used
I = ideal(A^3*C^2-B^5,A^5*D^2-B^7,A^2*D^5-C^7,B^2*D^3-C^5)
L = solvePDE(I)
I' = getPDE L	     
I == I' -- check the ideals are equal
amult(I)
sum apply(primaryDecomposition I, Q -> amult Q)
-- The naive number of Noetherian operators is: 1044. 
-- But, amult(I) = 207.
----------------------------------------------------
----------------------------------------------------



----------------------------------------------------
----------------------------------------------------
-- Example 6: Example 1.1 in the Introduction of our paper
R = QQ[x,y,z]
I = ideal(x*y*z^2, x*y^2*z, x^2*y*z, y^2*z^2, 
    2*x*y*z-x*z^2+y*z^3, 2*x*y*z-x^2*y+x^3*z,
    2*x*y*z-y^2*z+x*y^3)
L = solvePDE(I)
I' = getPDE L	     
I == I' -- check the ideals are equal
amult(I)
sum apply(primaryDecomposition I, Q -> amult Q)
-- The naive number of Noetherian operators is: 20. 
-- But, amult(I) = 7.
----------------------------------------------------
----------------------------------------------------


----------------------------------------------------
----------------------------------------------------
-- Example 7: Example 1.2 in the Introduction of our paper
R = QQ[x,y,z]
I = ideal(x^2*y, x^2*z, x*y^2, x*y*z^2)
L = solvePDE(I)
I' = getPDE L	     
I == I' -- check the ideals are equal
amult(I)
sum apply(primaryDecomposition I, Q -> amult Q)
-- The naive number of Noetherian operators is: 12. 
-- But, amult(I) = 5.
----------------------------------------------------
----------------------------------------------------
