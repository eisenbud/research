--David,
--Bernd and I are thinking about the following question--do you know a
--counterexample? It relates to our convexity statement. Namely, let
--S have dimension n, dim (S/I) = 0. Is
--t_n(S/I) \leq a_1t_{q_1}(S/I) + ... + a_kt_{q_k}(S/I)
--whenever a_1q_1+ ... + a_kt_k = n?
--Craig and Bernd


--First case of interest is probably 6 variables, 3*t2>=6
-- need to keep the socle degree high,
--but kill the high degree relations
--on the generators of I.

S=kk[a..f]
n=4
i=(ideal(a,b))^n+(ideal(b,c))^n+
      (ideal(c,d))^n+(ideal(d,e))^n+
           (ideal(e,f))^n
bettiBounds(i)
F=res i
for t from 0 to length F list  max flatten degrees F_t
