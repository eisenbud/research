--This file shows that the ideal of 6 random points in the 
--plane is generated by products of linear forms.

-- Is it true for 2r+2 points in Pr?

restart
S=kk[a,b,c]
points=random(S^3, S^6)
points=id_(S^3)|
       matrix{{1_S},{1_S},{1_S}}|
       matrix{{1_S,3_S},{2_S, 7_S},{3_S,11_S}}
minors(3, points)--all nonzero entries shows all minors nonzero
--The following function works only if all the 2x2 minors of "points"
--are nonzero. Gives the linear form defining the line throug
--the pth and qth point.
L=(p,q)->sum(0..2, i->
     (if p==q then 0_S else
     (entries (gens minors (2,points_{p,q})))_0_i*S_i))
--the following is then the ideal of all the products of linear
--forms vanishing on the 6 points.
i=
ideal(L(0,1)*L(2,3)*L(4,5))+
ideal(L(0,2)*L(1,3)*L(4,5))+
ideal(L(0,3)*L(1,2)*L(4,5))+
ideal(L(0,1)*L(2,4)*L(3,5))+
ideal(L(0,2)*L(1,4)*L(3,5))+
ideal(L(0,4)*L(1,2)*L(3,5))+
ideal(L(0,1)*L(4,3)*L(2,5))+
ideal(L(0,4)*L(1,3)*L(2,5))+
ideal(L(0,3)*L(1,4)*L(2,5))+
ideal(L(0,4)*L(2,3)*L(1,5))+
ideal(L(0,2)*L(4,3)*L(1,5))+
ideal(L(0,3)*L(4,2)*L(1,5))+
ideal(L(4,1)*L(2,3)*L(0,5))+
ideal(L(4,2)*L(1,3)*L(0,5))+
ideal(L(4,3)*L(1,2)*L(0,5))


betti res i
(res i).dd_2

