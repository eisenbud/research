-*
restart
load "quiverComplexes.m2"
*-
--triangle:
a=3;
b=3;
c=2;
u=2;
v=1;
w=1;

kk = ZZ/32003
S = kk[x_(0,0)..x_(a-1,b-1), y_(0,0)..y_(b-1,c-1),z_(0,0)..z_(c-1,a-1)]

ab = genericMatrix(S,x_(0,0),a,b)
bc = genericMatrix(S,y_(0,0),b,c)
ca = genericMatrix(S,z_(0,0),c,a)

comp = ideal(ab*bc)+ideal(bc*ca)+ideal(ca*ab)
ranks =  minors(u+1, ab)+minors(v+1, bc)+minors(w+1, ca)

I= comp+ranks
codim I
minimalBetti I

---all examples we could compute of the triangle graph with sums of ranks condition
--were CM, and the ones with equality were Gorenstein.

--Claw
a=2;
b=2;
c=2;
d=2;
u=1;
v=1;
w=1;

kk = ZZ/32003
S = kk[x_(0,0)..x_(a-1,d-1), y_(0,0)..y_(b-1,d-1),z_(0,0)..z_(c-1,d-1)]

ad = genericMatrix(S,x_(0,0),a,d)
da = transpose ad
bd = genericMatrix(S,y_(0,0),b,d)
db = transpose bd
cd = genericMatrix(S,z_(0,0),c,d)
dc = transpose cd
trans = S**matrix{{0,1},{-1,0}}
one = id_(S^2)
zer =map(S^2, S^2, 0)
if d == 4 then trans = (zer|one)||(-one|zer)
trans

comp = ideal(ad*trans*db)+ideal(ad*trans*dc)+ideal(bd*trans*dc)
ranks =  minors(u+1, ad)+minors(v+1, bd)+minors(w+1, cd)

I= comp+ranks
codim I
minimalBetti I

--the examples were CM if we put in a symplectic form, as above (d = 2 or 4); and if
--the sum of the ranks u+v+w<= d (but not with 1,2,2 and 4.) (but if d=2, then
--any claw is CM since it's the scroll)
--is there a good answer for the claw with d = 3?

--under what circumstances can one specialize the matrices, eg to scroll matrices?

