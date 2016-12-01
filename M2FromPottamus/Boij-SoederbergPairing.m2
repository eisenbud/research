restart;
--- loadPackage "BoijSoederberg";
loadPackage "BGG"

---  I couldn't get nu(F) to have the correct bigrading needed for the pushforward
--  but I came up with a hacky workaround.


grPullback=(nu,F)->(
     p:=length F;
     G:=nu(F);
     C:=new ChainComplex;
     C.ring=target nu;
     K:= apply(p+1,i->(flatten degrees F_i));
     L:=apply(K,i->( apply(i,l-> (-1)*(degree nu(x_0^l)) ) ));
     apply(p+1,i-> C_i=T^(L_i));
     apply(toList(1..p),i->(  C.dd#i=map(C_(i-1),C_i,G.dd#i);));
     return C;
     );

--  also, I was having issues with turning a module into a chain complex.  so i introduced another workaround.

modToCC=(M)->(
     C:=new ChainComplex;
     C.ring=ring M;
     C#0=M;
     return C
     );


---  Input:  F a graded complex of free S-modules, and E an arbitrary S-module.
---  Output: The product F\cdot E^~, where E^~ is the sheaf associated to E.
pair=(F,E)->(
     G=grPullback(nu,F)**grPullback(p1, res E);
     directImageComplex(G)     
     );

end;
--
--
--
--
--
--
--
--
--
--
--
--


restart;
load "pairing.m2"
--- This is the setup.
kk=ZZ/101
n=2;
S=kk[x_0..x_n];
A=kk[t];
T=A[y_0..y_n];
---  these are the two different maps that we pull back along.
nu=map(T,S,apply(n+1,i-> y_i*t),Degree=>{i,i})
p1=map(T,S,apply(n+1,i-> y_i))


---  These are a few examples.
F=res(S^1/(x_0,x_1,x_2));
C=pair(F,S^{1:0})
--  In this example, C is the product of the complex F and the structure sheaf on PP^2.
HH^0 C

--  Here's an example with a different F and with Omega^1_{PP^2}
m=ideal vars S
F=res (S^1/m^2)
E=ker matrix{{x_0,x_1,x_2}}
C=pair(F,E**S^{1:2})
betti C
HH^0 C

F=res (S^1/(x_0,x_1,x_2^2))
betti pair(F,S^{1:-1})

-- intersecting a conic and a quartic, the pairing has rank 8.
-- but the pairing isn't commutative.

F=res (S^1/(random(2,S)))
M=S^1/(random(4,S))
betti pair(F,M)

G=res (S^1/(random(4,S)))
N=S^1/(random(2,S))
betti pair(G,N)


