herzog=(phi,rho,L)->(
     d:=#L;
     R:=ring phi#0;
     F:=target phi#0;f:=rank F;
     r:=rank target rho;
     D1:=apply(d,i->map(R^(f),R^{f:-1},L#i*(id_F)));
     D0:=map(R^(f),R^{f:-1},0*(id_F));
     apply(d,t->(
	       LM:=apply(d,i->apply(d,j->
	       if i==j then 
		    (if t-i>=0 then phi#(t-i) else phi#(t-i+d))**rho^0
	       else if i+1==j or (i==d-1 and j==0) then
	       	     D1#i**(if t-i>=0 then rho^(t-i) else rho^(t-i+d))
	       else D0**rho^0));
               M:=LM#0#0;
               for j from 1 to d-1 do M=M|LM#0#j;
               for i from 1 to d-1 do (N=LM#i#0;
	           for j from 1 to d-1 do N=N|LM#i#j;
	       	   M=M||N);
	       M))
     )

