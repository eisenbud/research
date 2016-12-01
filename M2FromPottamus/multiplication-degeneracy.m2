--A file to study Harris/Huizenga's question:
--If S = kk[s,t], what is the codim of the locus in
--(V,W) \in Gr(v,S_d) x Gr(w, S_e) such that the map
--V ** W --> S_(d+e) fails to have maximal rank?
expectedCodimension = method(Options => {FirstSpaceGeneric => false})
--viewHelp options
expectedCodimension (List, List) := opts -> (vList,wList) -> (
     v := vList_0; --dim V
     d := vList_1; --degree of forms in V
     w := wList_0; -- dim W
     e := wList_1; -- degree of forms in W
     ec = 1+abs(v*w-d-e-1);
     if v*w>=d+e+1 and opts.FirstSpaceGeneric then 
          ec = min(ec,w-1) else
	  ec = min(ec,v-1,w-1);
     ec)
     

md = method(Options => {FirstSpaceGeneric => false})
md(List, List) := opts -> (vList, wList) -> (
     --vList = {dim V, degree of V}, and similarly for wList
     --the program outputs
     kk = ZZ/32003;
     S = kk[s,t];
     (v,d) = (vList_0, vList_1);
     (w,e) = (wList_0, wList_1);     
     if v>d+1 then error("v too large for d");
     if w>e+1 then error("w too large for e");     
     D = d+e+1;

--     if the multiplication should be onto, throw in the codim of one of the series having a base point:
     ec = expectedCodimension(vList,wList,FirstSpaceGeneric => opts.FirstSpaceGeneric);
--     ec = 1+abs(v*w-d-e-1);
--     if v*w>=d+e+1 then ec = min(ec,v-1,w-1); 

     T = kk[x_(0,0)..x_(v-1,d-v), y_(0,0)..y_(w-1,e-w),s,t];
     --z is a homogenizing variable
--handle the cases v = d+1 and w = e+1

     if v == d+1 then 
          V = (id_(T^v))*(transpose sub(basis(d, S^1),T))
     else(
        if opts.FirstSpaceGeneric=>false then 
          vm = (id_(T^v))|transpose genericMatrix(T,x_(0,0),d+1-v,v)
        else vm = (id_(T^v))|random(T^v, T^(d+1-v));
          V = vm*transpose sub(basis(d, S^1),T)
          );
     if w == e+1 then W = (id_(T^w))*(transpose sub(basis(e, S^1),T)) else (
     wm = (id_(T^w))|transpose genericMatrix(T,y_(0,0),e+1-w,w);     
     W = wm*transpose sub(basis(e, S^1),T));

     monoms = sub(basis(d+e, S^1),T);
     VW = flatten (V*transpose W);
     M = contract(transpose monoms, VW);
     -- map with source rank =  vw, target rank = D
     if v*w < D then M = transpose M;
     R = kk[z_0..z_ec];
--     error();
     makeSmall = map(R,T,
	  (matrix{{z_1..z_ec}})*(random(R^ec,R^(v*(d+1-v)+w*(e+1-w))))|matrix{{0_R,0_R}}
	            );
     MR = coker homogenize(makeSmall M, z_0);
     dimMR = dim MR;
     if dimMR !=1 then (
	  MR0 = MR/z_0;
	  dimMR0 = dim MR0;
	  if dimMR0 == dimMR then (
--	       print "saturating";
	       MR1 = MR/saturate(0*MR,z_0); -- 0_MR doesn't work here
	       dMR1 = dim MR1;
	       excess = if dMR1 >=0 then dMR1-1 else 0;
	       return (ec,excess, degree MR1)));
     (ec, dimMR-1)
)

md(List,List,ZZ) := (vList,wList,flag) ->(
     --same as the above, but take the space V to be
     --generic of its dimension (and fixed) and 
     --build the codim of
     --base points into the "expected" codim.
     kk = ZZ/32003;
     S = kk[s,t];
     (v,d) = (vList_0, vList_1);
     (w,e) = (wList_0, wList_1);     
     D = d+e+1;
     ec = if v*w<=d+e+1 then 1+abs(v*w-d-e-1) else
           min(1+abs(v*w-d-e-1), w-1);
     T = kk[x_(0,0)..x_(v-1,d-v), y_(0,0)..y_(w-1,e-w),s,t];
     --z is a homogenizing variable
--handle the cases v = d+1 and w = e+1

     if v == d+1 then V = (id_(T^v))*(transpose sub(basis(d, S^1),T)) else (
     vm = (id_(T^v))|random(T^v, T^(d+1-v));
--     vm = (id_(T^v))|transpose genericMatrix(T,x_(0,0),d+1-v,v);     
     V = vm*transpose sub(basis(d, S^1),T));
     if w == e+1 then W = (id_(T^w))*(transpose sub(basis(e, S^1),T)) else (
     wm = (id_(T^w))|transpose genericMatrix(T,y_(0,0),e+1-w,w);     
     W = wm*transpose sub(basis(e, S^1),T));

     monoms = sub(basis(d+e, S^1),T);
     VW = flatten (V*transpose W);
     M = contract(transpose monoms, VW);
     -- map with source rank =  vw, target rank = D
     if v*w < D then M = transpose M;
     R = kk[z_0..z_ec];
--     error();
     makeSmall = map(R,T,
	  (matrix{{z_1..z_ec}})*(random(R^ec,R^(v*(d+1-v)+w*(e+1-w))))|matrix{{0_R,0_R}}
	            );
     MR = coker homogenize(makeSmall M, z_0);
     dimMR = dim MR;
     if dimMR !=1 then (
	  MR0 = MR/z_0;
	  dimMR0 = dim MR0;
	  if dimMR0 == dimMR then (
	       MR1 = MR/saturate(0*MR,z_0); -- 0_MR doesn't work here
	       dMR1 = dim MR1;
	       excess = if dMR1 >=0 then dMR1-1 else 0;
	       return (ec,excess, degree MR1)));
     (ec, dimMR-1)
)
     
end
restart
load "multiplication-degeneracy.m2"

expectedCodimension({4,6},{5,5}, FirstSpaceGeneric => false)
expectedCodimension({4,6},{5,5}, FirstSpaceGeneric => true)
expectedCodimension({4,6},{5,5})
md({3,6},{5,5}, FirstSpaceGeneric => true)
viewHelp Options
M = md({3,2}, {3,2})
M = md({3,2}, {2,2})
M = md({3,2}, {2,2},1)

--M = md({3,6}, {3,5}) -- too hard for impatient people
time M = md({3,5}, {3,5})




--pencil of conics case:
--is deffective whenever the expected codim is >1, the
--codim in which the pencil of conics has a base point.
--Non-defective in other cases.
L=for v from 2 to 2 list (
     for w from 2 to 6 list (
	  for d from 2 to 2 list (
	       for e from max(d,w-1) to 7 list 
		    ({v,d},{w,e}))))
L1 = ultimate(flatten, L)
#L1
L2 = sort apply(L1, o -> prepend(1+abs(o_0_0*o_1_0-o_0_1-o_1_1-1), o))

time L3 = apply(L2, o->(
	  mo = md drop(o,1);
	  if mo_1!=0 then print(o, mo);
	  (o,mo)));

time L3 = apply(L2, o->(
	  mo = md append(drop(o,1),1);
	  if mo_1!=0 then print(o, mo);
	  (o,mo)));


--net of conics case:	  
L=for v from 3 to 3 list (
     for w from 2 to 6 list (
	  for d from 2 to 2 list (
	       for e from max(d,w-1) to 7 list 
		    ({v,d},{w,e}))))
L1 = ultimate(flatten, L)
#L1
L2 = sort apply(L1, o -> prepend(1+abs(o_0_0*o_1_0-o_0_1-o_1_1-1), o))

time L3 = apply(L2, o->(
	  mo = md drop(o,1);
	  if mo_1!=0 then print(o, mo);
	  (o,mo)));
time L3 = apply(L2, o->(
	  mo = md append(drop(o,1),1);
	  if mo_1!=0 then print(o, mo);
	  (o,mo)));

--degrees > 2 case
L=for v from 2 to 6 list (
     for w from 2 to 6 list (
	  for d from max(3,v-1) to 5 list (
	       for e from max(d,w-1) to 5 list 
		    ({v,d},{w,e}))))
L1 = ultimate(flatten, L)
#L1
L2 = sort apply(L1, o -> prepend(1+abs(o_0_0*o_1_0-o_0_1-o_1_1-1), o))
#(L2 = select(L2, i->i_0<=5))
L2
time L3 = apply(L2, o->(
	  mo = md drop(o,1);
	  if mo_1!=0 then print(o, mo);
	  (o,mo)));

--degrees > 2 case with one space generic
L=for v from 2 to 6 list (
     for w from 2 to 6 list (
	  for d from max(3,v-1) to 12 list (
	       for e from max(d,w-1) to 8 list 
		    ({v,d},{w,e}))))
L1 = ultimate(flatten, L)
#L1
L2 = sort apply(L1, o -> prepend(1+abs(o_0_0*o_1_0-o_0_1-o_1_1-1), o))
#(L2 = select(L2, i->(5< i_0 and i_0<=7)))
L2
	  
time L3 = apply(L2, o->(
	  mo = md append(drop(o,1),1);
	  if mo_1!=0 then print(o, mo);
	  (o,mo)));




