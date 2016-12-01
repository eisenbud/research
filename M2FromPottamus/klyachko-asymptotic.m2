--compute the cohomology of a bundle on P1xP1 that can occur as an asymptotic pushforward under the
--Frobenius maps, after a description by Payne

--A rank r bundle E is associated with:
--Four filtrations
--let 
--J={j0,j1,j2,j3} 
--be the unique places where the filtrations have the intermediate values,
--which are of dimensions 
--E = {e0,e1,e2,e3}}
--ei, 0\leq ei\leq r.
--A bundle B is a sequence
--B = (r,J,E) 
--a character is a list of two integers
--u = {u0,u1}

--make the line bundle \CO(i,j)
LB = (i,j) -> (
     r := 1;
     J := {-i,-j,0,0};
     E := {1,1,1,1}; --makes j_i the first spot at which the filt is 1
     (r,J,E)
     )
--twist with the line bundle \CO(i,j)
twist = (B,a,b) ->(
      (r,J,E) := B;
      (r,{J_0-a,J_1-b,J_2,J_3},E)
      )
tN=(a,b,c)->( -- 0 if no two are nonzero
     if abs(a*b)+abs(a*c)+abs(b*c)>0 then 1 else 0
     )
tZ=(a,b,c)->( -- 0 if no two are nonzero
     if a==0 and b==0 and c==0 then 0 else 1
     )

----------------------------
--auxilliary computations     
dimfilt=(B,i,v)->(
     --dimension of ith filtration at place v. Typically v is one component of a character.
     (r,J,E) := B;
     if v<J_i then 0
     else if v == J_i then E_i
     else r)

sumu = (B,u)  ->  dimfilt(B,0,u_0)+dimfilt(B,1,u_1)+dimfilt(B,2,-u_0)+dimfilt(B,3,-u_1)
----------------------------
---------------------------
h0 = method()
h0(Sequence, List) := (B,u) -> (
     r := B_0;
     max(sumu(B,u)-3*r,0)
     )

h0(ZZ, List, List) := B -> (
     (r,J,E) := B;
     h := 0;
     for u0 from J_0 to -J_2 do(
	  for u1 from J_1 to -J_3 do h = h + h0(B,{u0,u1}));
     h)

h1 = method()
h1(Sequence, List) := (B,u) -> h0(B,u) + h2(B,u) - chi(B,u)
h1(ZZ, List, List) := B -> h0 B + h2 B - chi B

h2 = method()

h2(Sequence, List) := (B,u) -> (
     r := B_0;
     max(r-sumu(B,u),0)
     )

h2(ZZ, List, List) := B -> (
    (r,J,E) := B;
     h := 0;
     for u1 from -J_2 to J_0 do(
	  for u2 from -J_3 to J_1 do h = h + h2(B,{u1,u2}));
     h)

chi = method()

chi(Sequence, List) := (B,u) -> (
     r := B_0;
     m1 := max(dimfilt(B,0,u_0)+dimfilt(B,1,u_1)-r,0);
     m2 := max(dimfilt(B,1,u_1)+dimfilt(B,2,-u_0)-r,0); 
     m3 := max(dimfilt(B,2,-u_0)+dimfilt(B,3,-u_1)-r,0);
     m4 := max(dimfilt(B,0,u_0)+dimfilt(B,3,-u_1)-r,0);
     r - sumu(B,u) + m1+m2+m3+m4
     )

chi(ZZ, List, List) := B -> (
    (r,J,E) := B;
     h := 0;
     for u1 from min(J_0, -J_2)  to max(J_0, -J_2) do(
	  for u2 from min(J_1,-J_3) to max(J_1,-J_3)  do h = h + chi(B,{u1,u2}));
     h)

testNatural=(B,a)->(
     map(ZZ^(2*a+1), ZZ^(2*a+1), (p,q)->(
	       tN(h0 twist(B,p-a,q-a),h1 twist(B,p-a,q-a),h2 twist(B,p-a,q-a))
     )))

displayZeros=(B,a)->(
     map(ZZ^(2*a+1), ZZ^(2*a+1), (p,q)->(
	       tZ(h0 twist(B,p-a,q-a),h1 twist(B,p-a,q-a),h2 twist(B,p-a,q-a))
     )))
displaychi=(B,a)->(
     map(ZZ^(2*a+1), ZZ^(2*a+1), (p,q)->(
	       chi twist(B,p-a,q-a))))

end
restart
load "klyachko-asymptotic.m2"
(r,J,E) = LB(0,0)
B = LB(0,0)

dimfilt(B,1,1)
sumu (B,{0,0})
h0(B,{0,0})
h2(B,{0,0})
chi(B,{0,0})
h1(B,{0,0})

map(ZZ^10, ZZ^10, (a,b) -> h0 LB(-a+5,b-5)) 
map(ZZ^10, ZZ^10, (a,b) -> h1 LB(-a+5,b-5)) 
map(ZZ^10, ZZ^10, (a,b) -> h2 LB(-a+5,b-5)) 
map(ZZ^10, ZZ^10, (a,b) -> chi LB(-a+5,b-5)) 

T = (2,{0,0,0,0},{1,2,2,1})


map(ZZ^10, ZZ^10, (a,b) -> h0 twist(T,a-6,b-6)) 
map(ZZ^10, ZZ^10, (a,b) -> h1 twist(T,a-6,b-6)) 
map(ZZ^10, ZZ^10, (a,b) -> h2 twist(T,a-6,b-6)) 

map(ZZ^10, ZZ^10, (a,b) -> chi twist(T,a-6,b-6)) 

T = (5,{0,0,0,0},{1,2,3,4})
testNatural(T,6)
displayZeros(T,6)
displaychi(T,6)

time tally apply(100,i->(
	  r=2+random 10;
	  T = (r,{0,0,0,0},apply(4,j->random r));
	  testNatural(T,6)==0)
)
r=3
time L= flatten flatten flatten  apply(3, u0->  apply(3, u1->  apply(3, u2 -> apply(3, u3->(
	  T = (r,{0,0,0,0},{u0,u1,u2,u3}))))))
L_0
time Lgood = select (L, T -> testNatural(T,6)==0)
Lbetter = select(Lgood, T-> sum(T_2) > 3)
U=unique(apply(Lbetter, T->displaychi(T,6)));
time V=apply(U,u->first select(Lbetter, T-> u==displaychi(T,6)));
apply(V, v->last v)
W={(3,{0,0,0,0},{1,1,2,2}),(3,{0,0,0,0},{1,1,1,1}),(3,{0,0,0,0},{0,1,1,2})}
apply(W,w->displaychi(w,6))
)
displaychi((5,{0,0,0,0},{2,2,3,3}),6)
testNatural((5,{0,0,0,0},{2,2,3,3}),6)

SBundle = n-> {n+1,{0,0,0,0}


testNatural(Lgood_7,6)
Lgood_7
displayZeros(T,6)
displaychi(T,6)

