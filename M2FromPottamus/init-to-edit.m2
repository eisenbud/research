-- This is a sample init.m2 file provided with Macaulay2.
-- It contains Macaulay 2 code and is automatically loaded upon
-- startup of Macaulay2, unless you use the "-q" option.

-- Uncomment the following line to cause Macaulay2 to load "start.m2" in the current working directory upon startup.
-- if fileExists "start.m2" then load(currentDirectory|"start.m2")

-- Uncomment and edit the following lines to add your favorite directories containing Macaulay 2
-- source code files to the load path.  Terminate each directory name with a "/".
-- path = join( { homeDirectory | "src/singularities/", "/usr/local/src/M2/" }, path )

-- Uncomment the following line if you prefer Macaulay2's larger 2-dimensional display form for matrices.
-- compactMatrixForm = false

-- Uncomment and edit the following line if you would like to set the variable kk to your favorite field.
-- kk = ZZ/101

-- Uncomment and edit the following line if you don't need to be informed of the class of a sequence 
-- after it is printed by M2.  This works for other classes, too.
-- Sequence#{Standard,AfterPrint} = Sequence#{Standard,AfterNoPrint} = identity

-- Uncomment and edit the following line to set a default printwidth for situations where M2 doesn't know the width
-- of your terminal.
-- if printWidth == 0 then printWidth = 100

-- Uncomment and edit the following line to preload your favorite package.
-- needsPackage "StateTables"


--path = append(path,"/Users/DE/Documents/M2")

printWidth=110
--path = prepend("/Users/de/documents/M2/" ,path)
--path = prepend("/Users/de/Documents/M2-dropbox", path)
--path = prepend("/Users/de/Dropbox/Documents/M2-dropbox", path)
--path = prepend("/Users/de/M2/M2/Macaulay2/packages/", path)
path = prepend("/Users/de/research/", path)
path = prepend("./",path)
--print"Redefined BettiTally, ^[]"

{*
///--rewrite of the betti code
net BettiTally := v -> (
     v' := new MutableHashTable;
     scan(pairs v, (key,n) -> (
	       (i,d) := key;
	       d = if d#?0 then d#0 else 0;
                 -- just use the first component of the degree
	       d = d-i; -- skew the degrees in the usual way
	       key = (d,i);
	       if v'#?key then v'#key = v'#key + n else v'#key = n;
	       ));
     v = v';
     k := keys v;
     fi := first \ k;
     la := last  \ k;
     mincol := min la;
     maxcol := max la;
     minrow := min fi;
     maxrow := max fi;
     v = table(toList (minrow .. maxrow), toList (mincol .. maxcol),
       (i,j) -> if v#?(i,j) then v#(i,j) else 0);
     leftside := splice {"", "total:", apply(minrow .. maxrow, i ->
        toString i | ":")};
     totals := apply(transpose v, sum);
     v = prepend(totals,v);
     v = applyTable(v, bt -> if bt === 0 then "." else toString bt);
     v = prepend(toString \ toList (mincol .. maxcol), v);
     v = apply(leftside,v,prepend);
     netTable(v, Alignment => Right, HorizontalSpace => 1, BaseRow => 1))
///

--rewrite of ^[]

Ideal ^ Array := (I,a) -> (
     if #a =!= 1 then error "expected an integer";
     if not instance(a#0,ZZ) then error "expected an integer";
     r := a#0;
     ideal(apply(numgens I, i -> I_i^r)))


Matrix ^ Array := (m,a) -> (
     if #a =!= 1 then error "expected an integer";
     if not instance(a#0,ZZ) then error "expected an integer";
     r := a#0;
     dm:= r*flatten degrees target m;
     em:= r*flatten degrees source m;
     map((ring m)^(-dm),(ring m)^(-em),(u,v)->(m_(u,v)^r)))


document{Key => frobeniusPower,
     Headline => "Frobenius Power of ideal or matrix",
Inputs => {"M=>Ideal", "M=>Matrix" , "d=>ZZ"},
Usage => "M^[d], where M is an ideal or matrix and d is an integer,
     returns the d-th Frobenius power of M. If M is a matrix, then all
     row and column degrees are multiplied by d",
EXAMPLE lines ///
kk=ZZ/32003
S=kk[a,b,c,d]
m=matrix{{a,b},{c,d}}
m^[2]
(ideal vars S)^[2]
///
}

*}
see = method()
--methods for Matrix, Ideal, Module, List
see(Matrix):= (M)-> (
  if ((rank source gens M <10) and (rank target gens M <10)) then print M;
     betti M)

see(Ideal) := (I) -> (
if rank source gens I < 5 then print I else
if rank source gens I < 30 then 
                      print transpose gens I;
    betti gens I)

see(Module) := (M) -> (
    if isFreeModule M then (
       print "Free module";
       degrees M)            else
         (N:= prune M;
         if (rank source gens M <10 and 
             rank target gens N <10)   then print N;
     betti gens N)
           )

see(List) := (L) -> scan(L, i->print i)



randomIdealElements=(I,L)->(
ideal((gens I)*random(source gens I, (ring I)^(-L))))

document{Key=> randomIdealElements,
Headline=> "randomIdeal(I=Ideal,L=List of ZZ)","--
Returns an Ideal generated by random elements of I
with degrees specified by the elements of L.",
EXAMPLE lines ///
kk=ZZ/32003
S=kk[a,b,c,d]
i=ideal"a2,ab,c5"
j=randomIdealElements(i,{2,3,6})
degrees j
degrees diff(c, gens j)=={{{0}}, {{1}, {2}, {5}}}
///
}



document{Key=>  see,
Headline => "--see","displays an Ideal, Module, Matrix, or List",
Usage=>
"Applied to an object of type Ideal, Module, Matrix, or List,
see displays useful information about the object.
The format and content depend on the size of the object."}

--The following returns the submodule generated by the degree d
--generators of the module A
submoduleByDegrees=(A,Deglist)->(
     F := target presentation A;
     L := flatten degrees F;
     L1:= toList select(0..(rank F)-1,i->member(L_i,Deglist));
     prune (image F_L1/(image presentation A)))

{*
document{Key => submoduleByDegrees,
     Headline => "Submodule of A generatd by generators of degrees listed",
Inputs => {"A=>Module", "Deglisst=>List of ZZ"},
Usage => "SubmoduleByDegrees(A, Deglist)",
EXAMPLE lines ///
kk=ZZ/7
S=kk[a,b,c,d]
m=coker random(S^{2,4,6},S^{-1,3})
betti m
betti submoduleByDegrees(m, {-4,-5,-6})
///
}


--the following takes a matrix, and returns the submatrix
--whose rows are of degree d and whose columns are of degree e
*}
submatrixByDegs=(f,D,E)->(
     --D,E are lists of degrees for rows and cols, respectively
     Ltarget := flatten degrees target f;
     Lsource := flatten degrees source f;
     Lt:= toList select(toList(0..(rank target f)-1),i->member(Ltarget_i, D));
     Ls:= toList select(toList(0..(rank source f)-1),i->member(Lsource_i, E));
     f_Lt^Ls
     )



document{Key => submatrixByDegs,
Headline => "submatrix of elements with given row and col degrees",
Inputs => {"(Matrix, List of ZZ, List of ZZ)"},
Usage => "submatrixByDegs(m, rowdegs, coldegs)",
EXAMPLE lines ///
kk=ZZ/2
S=kk[a,b,c,d]
m=random(S^{2,4,6},S^{-1,3})
betti m
n= submatrixByDegs(m,{3},{4})
betti n
n=submatrixByDegs(m,{-2,-4},{1})
betti n
///
}     

-----------------------------Some special purpose functions

catalecticant = (R,v,m,n) -> 
                 map(R^m,n,(i,j)-> R_(i+j+v))

document{Key=>  catalecticant,
Headline => "--catalecticant(R=Ring,i=ZZ,j=ZZ,v=ZZ)","Returns
a Matrix whose (i,j) entry is the i+j+v variable of R."}

-----------------------------
MultiDegs = n-> entries (transpose map(ZZ^1,ZZ^n,matrix{{n:1}}) |id_(ZZ^n))

document{Key=>  MultiDegs,
     Headline => "MultiDegs(ZZ)",
     Usage=> "returns a matrix over ZZ suitable for 
     defining the ZZ^n-grading on a polynomial ring in n variables,
     via the option Degrees.",
     EXAMPLE lines ///
     R = kk[vars(0..n-1), Degrees=>MultiDegs n]
     ///
     }

----------------------------
HF = (degs, M) -> toList (
     apply(degs,i->hilbertFunction(i,M)))
document{Key=>  HF,
     Headline => "--HF(Sequence or List,Module)",
     Usage=>"using hilbertFunction(ZZ,Module),
     HF returns a Sequence or List
     of the values of the Hilbert function of the Module
     at the integer arguments specified by the Sequence or List."}

----------------------------
--for some reason we also did it with small letters
hf=(range, m)->(
       apply(range,i->hilbertFunction(i, m)))
document{Key=>  hf,
     Headline => "--hf(Sequence or List,Module)",
     Usage=>"using hilbertFunction(ZZ,Module),
     hf returns a Sequence or List
     of the values of the Hilbert function of the Module
     at the integer arguments specified by the Sequence or List."}

----------------
--for arrangements:

--NB: these programs should be replaced by Sorin's package.

--Construction of Orlik-Solomon algebras
--The idea is to code the dependent sets (circuits) as 
--monomials, then apply an operator that makes each monomial
--into the corresponding Orlik-Solomon relation.

--The following takes a monomial in the exterior alg and manufactures
--an Orlik-Solomon relation from it (the alt sum of the derivatives
--with respect to the variables in the monomial)
orlikSolomon1 = n-> (
     d:=(degree n)_0;
     (compress diff(vars R, n))*
               (transpose map(R^1,R^d,{{d:1}}))
     )

--now the same thing for a whole ideal:
orlikSolomon = i->(
     p:=rank source gens i;
     j:=ideal(orlikSolomon1(i_0));
     scan(p-1,t->(j=j+ideal(orlikSolomon1(i_(t+1)))));
     j)
---------------------
--If M is a module over the polynomial ring S, 
--E is the corresponding exterior algebra, e\in E_1,
--let \kappa(e) be the residue field of Proj S at the point e.
--The following returns Tor(M,\kappa(e)), regarded as an E-module.
{*
torModule=(M,e,E)->(
     reg := regularity M;
     mt  := presentation truncate(reg,M);
     n   := tranpose symExt(mt,E);
     F   := res coker n;
     N   := kernel transpose F.dd_1;
     mape:= map(E^1,E^{-1},matrix{{e}});
     prune (kernel ((E^{1}**mape)**N)/(image (mape**N))))

--This gives the free resolution of the dual module (the dual
--of the injective resolution of Tor)
resDualTor=(M,e,E)->(
     N := torModule(M,e,E);
     Nd:= Hom(N,E);
     res Nd)


--The following returns the dual of the part
-- of the d-th linear strand of the 
--Tor(M,\kappa(e)) generated at the start, as a module over E:
strand=(M,e,E,d)->(
     T := torModule(M,e,E);
     T1:= Hom(T,E);
     gensOfDeg(T1,d))
----------
*}
--generic Z/2-graded matrices
superGeneric=(p,evenrows,oddrows,evencols,oddcols)->(
     --make a generic matrix 
     --over a char p superalgebra
     --of pattern:
     --  size           evencols     oddcols
     --  evenrows      |even            odd |    =   |X  A|
     --  oddrows       |odd             even|        |B  Y|
     --
     -- the diagonal entries will all be deg 2, the lower left deg 3,
     -- the upper right deg 1
     --
     --BUG:
     --gives error msg if there are no rows or no cols at all.
kk:=ZZ/p;
R:=kk[X_{0,0}..X_{evenrows-1,evencols-1},
     A_{0,0}..A_{evenrows-1,oddcols-1},
     B_{0,0}..B_{oddrows-1,evencols-1},
     Y_{0,0}..Y_{oddrows-1,oddcols-1},
     SkewCommutative=>true, 
     Degrees=>{(evenrows*evencols):2,
	       (evenrows*oddcols):1,
	       (oddrows*evencols):3,
	       (oddrows*oddcols):2}];
f:=(i,j)->if i<evenrows and j<evencols then X_{i,j} else
          if i>=evenrows and j<evencols then B_{i-evenrows,j} else
	   if i<evenrows and j>=evencols then A_{i,j-evencols} else
	    Y_{i-evenrows,j-evencols};
map(R^{evenrows:2,oddrows:3},
     R^{evencols:0,oddcols:1},
     table(evenrows+oddrows,evencols+oddcols,f))
)

gin=i->(
     R:=ring i;
     n:=numgens R;
     f:=map(R,R,random(R^1,R^{n:-1}));
     leadTerm f i)
    	      
--
kk = ZZ/32003;
--S = kk[a..e];
print""
print "kk = ZZ/32003"
--print "S=kk[a..e]"

