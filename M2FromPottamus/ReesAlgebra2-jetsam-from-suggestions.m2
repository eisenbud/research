

--from reesRegs.m2:
assymptoticDegree = method()
assymptoticDegree(Ideal, Module, RingElement) := (i,M,u) ->(
     --takes an ideal and a module over a polynomial ring, returns the
     --assymptotic degree of the generators of the module on the ideal.
     --Here u should be an element of i that is outside each minimal prime of M.
     igens := orderedMinGens i;
     A:= annihilator M;
     R:=(ring i)/A;
     jgens := substitute(igens,R);
     I:=reesIdeal(ideal igens, u);
     xVars:=ideal substitute(vars ring i, ring I) ;
     J:=mingens(I+xVars);
     T:=(ring I)/ideal J;
     s:=dim T-1;
     ti:=ideal((vars T)_{0..s});
     while (dim (T/ti))>0 do (
     	  s=s+1;
	  ti=ti+ideal(T_s));
     print s;
     degree igens_s
     )
assymptoticDegree(Ideal):= i -> assymptoticDegree(i, (ring i)^1, i_0)

orderedMinGens = i-> sort(mingens i, DegreeOrder=>Ascending)



whichGm0 = i ->(
     --This function returns the largest number m for which the ideal i satsifies
     --the condition
     --G_m: i_P is generated by <= codim P elements for all P with codim P < m.
     --
     --This version will work well only if the presentation matrix is small or very sparse.
     --In medium-large examples, unless the presentation matrix
     --is very sparse, the other version, "whichGm", seems much faster.
     --
     --BUG: When "minors" is fixed so that minors(n,i) returns 1 for negative i,
     -- the next line will not be necessary, and the function can
     --be replaced with "minors" in the code below
     correctedMinors:=(n,f)->(if n<=0 then ideal(1_(ring f)) else minors(n,f));
     --
     f:=presentation module i;
     q:=rank target f;
     d:=dim ring i;
     m=codim i;
          while m<d+1 and codim correctedMinors(q-m,f) > m do m=m+1;
     if m<=d then m else "infinity")
