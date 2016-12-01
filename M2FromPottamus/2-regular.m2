-- Some 2-regular triple structures on a rational normal curve.
-- According to our theorem, any such is split, and the nilpotent ideal is 1-regular.
-- Take the structure sheaf, as a module over P1, to be O + O(a) +O(b), where O(a)+O(b) is nilpotent, cube =0,
--and it square is contained in O(b).
-- need a,b >= -1, b >= 2a. The multiplication is determined by the above if we know O(2a) -> O(b),
-- that is, a form of degree b-1.

kk=ZZ/32003
d=2 -- degree of the reduced curve
a=-1
b=0

S=kk[s,t,x_0..x_d, y_0..y_(a+d+1), z_0..z_(b+d+1)]
F= s -- form of degree b-a in 2 auxiliary variables s,t

ixx=minors(2,map(S^2,S^{d:-1},(i,j)->x_(i+j)))
ixy=ideal(y_0..y_(a+d+1))*ideal(z_0..z_(b+d+1))
izz=(ideal(z_0..z_(b+d+1)))^2

Gyy= gens (ideal(y_0..y_(a+d+1)))^2
y_i*y_j- 