--Caviglia's old examples of regularity quadratic in the degree of the 4 generators in 6 vars.
kk = ZZ/101

S = kk[x,y,a,b]
--reg n^2-1
Cav = n-> I = ideal(x^n,y^n,x*a^(n-1)+y*b^(n-1))
for n from 2 to 10 do print regularity Cav n
--
S = kk[a,b,x,y,u,v]

--
S = kk[a,b,x,y,u,v]
--reg n^2+2, lower product of degrees than Cav
McC0 = n-> I = ideal(u^3,v^3, u^2*x^(n-2)+v^2*y^(n-2)+u*v*(x*a^(n-1)+y*b^(n-1)))
for n from 2 to 10 do print regularity McC2 n

--conjecturally cubic regularity:
McC1 = n-> I = ideal(u^n,v^n, u*x^(n-1)+v*y^(n-1)+u*v*(x*a^(n-1)+y*b^(n-1)))
McC = n-> I = ideal(u^n,v^n, u^2*x^(n-2)+v^2*y^(n-2)+u*v*(x*a^(n-1)+y*b^(n-1)))
betti res McC 3
for n from 2 to 10 do print regularity McC n

--
--conjecturally super-polynomial examples
Mc3 = n->(
S := kk[X_0..X_n,Y_0..Y_n];
I := ideal 0_S;
J := ideal 0_S;
if n==1 then I =ideal(X_1^2, Y_1^2, X_1*X_0+Y_1*Y_0);
if n>1 then (
    J = sub(Mc3 (n-1), S);
    I = ideal( X_n^(2*n), Y_n^(2*n), X_n^2*J_0+Y_n^2*J_1+X_n*Y_n*J_2)
    );
I)

(I = Mc3 3): ideal vars ring I

