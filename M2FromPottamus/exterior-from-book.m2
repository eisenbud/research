From dan@math.uiuc.edu Fri Aug 31 09:06:31 2001
Received: from ep2.msri.org [198.129.64.227] 
	by rafiki.msri.org with esmtp (Exim 2.05 #1 (Debian))
	id 15cqoQ-0004n6-00; Fri, 31 Aug 2001 09:06:30 -0700
Received: from charisma.math.uiuc.edu [130.126.108.20] 
	by ep2.msri.org with esmtp (Exim 3.12 #1 (Debian))
	id 15cqoQ-00049v-00; Fri, 31 Aug 2001 09:06:30 -0700
Received: from u00.math.uiuc.edu (u00.math.uiuc.edu [130.126.108.30])
	by charisma.math.uiuc.edu (8.11.1/8.11.1) with ESMTP id f7VG6Td23331
	for <de@msri.org>; Fri, 31 Aug 2001 11:06:30 -0500 (CDT)
Received: (from dan@localhost)
	by u00.math.uiuc.edu (8.11.1/8.11.1) id f7VG6Ta02190;
	Fri, 31 Aug 2001 11:06:29 -0500 (CDT)
Date: Fri, 31 Aug 2001 11:06:29 -0500 (CDT)
Message-Id: <200108311606.f7VG6Ta02190@u00.math.uiuc.edu>
X-Authentication-Warning: u00.math.uiuc.edu: dan set sender to dan@math.uiuc.edu using -f
From: "Daniel R. Grayson" <dan@math.uiuc.edu>
To: de@msri.org
In-reply-to: <20010831085059.A13969@snoop.msri.org> (message from David
	Eisenbud on Fri, 31 Aug 2001 08:50:59 -0700)
Subject: Re: code from m2book
References:  <20010831085059.A13969@snoop.msri.org>
Status: RO
X-Status: A
Content-Length: 5954
Lines: 175

   Date: Fri, 31 Aug 2001 08:50:59 -0700
   From: David Eisenbud <de@msri.org>
   Reply-To: de@msri.org

   Dear Dan,

	   After all the revisions etc, I find I don't have a file
   containing the final versions of the code from my chapter
   with Wolfram in the M2 book! Do you have a way of separating that
   from the text?  I think that, not only for my
   chapter, it would be very valuable to have code sources on
   the web, on the M2 page, or in a directory in the M2 release.

   For the moment my interest is immediate: I'm going to a conference
   on this stuff in a week, leaving town in a few hours but passing
   by Oberwolfach where I could presumably connect to the stuff. If
   it's easy for you to separate, would you be willing to mail
   me a file of code? If not, the TeX source for my chapter would
   do...

The separated code has been inserted into a file in the forthcoming M2
release.  Moreover, the automated testing procedure we run at compile time
checks to see whether the answers are still the same as they were before.
That helped us last month eliminate some bugs from the DEC Alpha version.

I include your file below.

-----------------------------------------------------------------------------

symExt = (m,E) ->(
     ev := map(E,ring m,vars E);
     mt := transpose jacobian m;
     jn := gens kernel mt;
     q  := vars(ring m)**id_(target m);
     ans:= transpose ev(q*jn);
     --now correct the degrees:
     map(E^{(rank target ans):1}, E^{(rank source ans):0}, 
         ans));
S=ZZ/32003[x_0..x_2];
E=ZZ/32003[e_0..e_2,SkewCommutative=>true];
M=coker matrix{{x_0^2, x_1^2}};
m=presentation truncate(regularity M,M);
symExt(m,E)
bgg = (i,M,E) ->(
     S :=ring(M);
     numvarsE := rank source vars E;
     ev:=map(E,S,vars E);
     f0:=basis(i,M);
     f1:=basis(i+1,M);
     g :=((vars S)**f0)//f1;
     b:=(ev g)*((transpose vars E)**(ev source f0));
     --correct the degrees (which are otherwise
     --wrong in the transpose)
     map(E^{(rank target b):i+1},E^{(rank source b):i}, b));
M=cokernel matrix{{x_0^2, x_1^2, x_2^2}};
bgg(1,M,E)
tateResolution = (m,E,loDeg,hiDeg)->(
     M := coker m;
     reg := regularity M;
     bnd := max(reg+1,hiDeg-1);
     mt  := presentation truncate(bnd,M);
     o   := symExt(mt,E);
     --adjust degrees, since symExt forgets them
     ofixed   :=  map(E^{(rank target o):bnd+1},
                E^{(rank source o):bnd},
                o);
     res(coker ofixed, LengthLimit=>max(1,bnd-loDeg+1)));
m = matrix{{x_0,x_1}};
regularity coker m
T = tateResolution(m,E,-2,4)
betti T
T.dd_1
sheafCohomology = (m,E,loDeg,hiDeg)->(
     T := tateResolution(m,E,loDeg,hiDeg);
     k := length T;
     d := k-hiDeg+loDeg;
     if d > 0 then 
        chainComplex apply(d+1 .. k, i->T.dd_(i))
     else T);
S=ZZ/32003[x_0..x_3];
E=ZZ/32003[e_0..e_3,SkewCommutative=>true];
m=koszul(3,vars S);
regularity coker m
betti tateResolution(m,E,-6,2)
betti sheafCohomology(m,E,-6,2)
M=sheaf coker m;
HH^1(M(>=0))
S = ZZ/32003[x_0..x_2];
U = coker koszul(3,vars S) ** S^{1};
k2 = koszul(2,vars S)
alpha = map(U ++ U, S^{-1}, transpose{{0,-1,0,1,0,0}});
alphad = map(S^1, U ++ U, matrix{{0,1,0,0,0,1}} * (k2 ++ k2));
F = prune homology(alphad, alpha);
betti  F
sortedBasis = (i,E) -> (
     m := basis(i,E);
     p := sortColumns(m,MonomialOrder=>Descending);
     m_p);
S=ZZ/32003[x_0..x_3];
E=ZZ/32003[e_0..e_3,SkewCommutative=>true];
koszul(2,vars S)
sortedBasis(2,E)
beilinson1=(e,dege,i,S)->(
     E := ring e;
     mi := if i < 0 or i >= numgens E then map(E^1, E^0, 0)
           else if i === 0 then id_(E^1)
           else sortedBasis(i+1,E);
     r := i - dege;
     mr := if r < 0 or r >= numgens E then map(E^1, E^0, 0)
           else sortedBasis(r+1,E);
     s = numgens source mr;
     if i === 0 and r === 0 then
          substitute(map(E^1,E^1,{{e}}),S)
     else if i>0 and r === i then substitute(e*id_(E^s),S)
     else if i > 0 and r === 0 then
          (vars S) * substitute(contract(diff(e,mi),transpose mr),S)
     else substitute(contract(diff(e,mi), transpose mr),S));
beilinson1(e_1,1,3,S)
beilinson1(e_1,1,2,S)
beilinson1(e_1,1,1,S)
U = (i,S) -> (
     if i < 0 or i >= numgens S then S^0
     else if i === 0 then S^1
     else cokernel koszul(i+2,vars S) ** S^{i});
beilinson = (o,S) -> (
     coldegs := degrees source o;
     rowdegs := degrees target o;
     mats = table(numgens target o, numgens source o,
              (r,c) -> (
                   rdeg = first rowdegs#r;
                   cdeg = first coldegs#c;
                   overS = beilinson1(o_(r,c),cdeg-rdeg,cdeg,S);
                   -- overS = substitute(overE,S);
                   map(U(rdeg,S),U(cdeg,S),overS)));
     if #mats === 0 then matrix(S,{{}})
     else matrix(mats));
S=ZZ/32003[x_0..x_2];
E = ZZ/32003[e_0..e_2,SkewCommutative=>true];
alphad = map(E^1,E^{-1,-1},{{e_1,e_2}})
alpha = map(E^{-1,-1},E^{-2},{{e_1},{e_2}})
alphad=beilinson(alphad,S);
alpha=beilinson(alpha,S);
F = prune homology(alphad,alpha);
betti  F
S = ZZ/32003[x_0..x_4];
E = ZZ/32003[e_0..e_4,SkewCommutative=>true];
beta=map(E^1,E^{-2,-1},{{e_0*e_2+e_1*e_3,-e_4}})
alpha=map(E^{-2,-1},E^{-3},{{e_4},{e_0*e_2+e_1*e_3}})
beta=beilinson(beta,S);
alpha=beilinson(alpha,S);
G = prune homology(beta,alpha);
betti res G
foursect = random(S^4, S^10) * presentation G;
IX = trim minors(4,foursect);
codim IX
degree IX
codim singularLocus IX
alphad = matrix{{e_4*e_1, e_2*e_3},{e_0*e_2, e_3*e_4},
                {e_1*e_3, e_4*e_0},{e_2*e_4, e_0*e_1},
                {e_3*e_0, e_1*e_2}};
alphad=map(E^5,E^{-2,-2},alphad)
alpha=syz alphad
alphad=beilinson(alphad,S);
alpha=beilinson(alpha,S);
FHM = prune homology(alphad,alpha);
betti res FHM
regularity FHM
betti sheafCohomology(presentation FHM,E,-6,6)
sect =  map(S^1,S^15,0) | random(S^1, S^4);
mapcone = sect || transpose presentation FHM;
fmapcone = res coker mapcone;
IX =  trim ideal fmapcone.dd_2;
codim IX
degree IX
codim singularLocus IX

