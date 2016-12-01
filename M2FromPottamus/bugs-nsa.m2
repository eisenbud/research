October 14, 1999
The following examples refer to:

HashTable{VERSION => 0.8.54                   }
                architecture => i586
                compile node name => geometry
                compile time => Jul 13 1999 13:01:00
                compiler => gcc 2.91
                dumpdata => true
                factory => true
                factory version => 1.2c
                gc version => 4.14 alpha 1
                libfac version => 0.3.1
                mp => false
                operating system => Linux
                operating system release => 2.2.10
--------------------------------------------------------


For an example of troublesome "help" in the documentation, see NonLinear.

In the tutorial doc on canonical curves that I have here 
(might not be the latest) it still makes a fuss about what the
source is, in a confusing way.

-------------------

"trim" and "prune":  As far as I could tell from
the documentation, trim works for ideals and rings as well as modules,
but... not matrices. On the other hand "prune" also sets "pruningMap",
which is not mentioned in "trim". Further, the doc for "prune" refers
to "trim" but not the other way round! I assume you prefer the word
"trim" but kept "prune" for compatibility? How about giving them both
the same documentation and the same capabilities (the union would be nice)
and mentioning in the doc that they are the same!

-----------------------
restart
S=(ZZ/101)[a]
i=ideal a^2
j=ideal a
R=S/i
-- the first of the following two expressions is fine; the second gives
-- an error. It would be nice if they were equivalent! Is their 
-- inequivalence at least documented?
substitute(j,vars R)+substitute(j,vars R)
substitute(j,vars (S/i))+substitute(j,vars (S/i))
--
-----------------------
dim works but "dimension" doesn't -- contrary to your policy
----------------------------------
This is a problem with Sorin's points.m2 (my version is now fixed!)
Some of the following documentation is bad
'randomPoints(R,n)' -- given a ring
	R, with r+1 variables, and a number n
	the script returns the homogeneous ideal of  
        n random points.
--This is ok


'randomPoints(r,n)'-- given positive
	integers r and n, returns the homogeneous ideal of  
        n random points over a polynomial ring in r+1 variables.
--At least say what poly ring (how did you choose char 101??)

'randomPoints(r,n, whatever)'--given a ring
        R, with r+1 variables, and a number n >= r+1,
        the script returns an r+1 x n matrix whose
        columns represent n random points including the
        standard simplex.
--Here "whatever" has to be an integer! Also, r should be R. Also,
--the script does not return the point matrix as it should, but the ideal!!
	
	
-----------
The following should produce the ideal of a cubic, I think,
but produces a quartic instead!
-------------------------------
restart
kk=ZZ/32003
R=kk[a,b,c]
map(R^{0},R^{-1,-1}, matrix{{a,b}})
betti pm -- this LOOKS ok but...
betti source pm
-- the source of "pm" is gen in degree 0, not 1 as it should be!!
betti random(source pm, R^{-3})
betti (pm*random(source pm, R^{-3})) -- source is degree 4, not 3
fcubic=ideal (pm*random(source pm, R^{-3}))
-- it's a quartic, not a cubic..
----------------------------------------------


The following gives wrong degrees in pushForward1 (the degrees
     should be the same as in the "kernel" command, just above)!
-----------------
restart
--loaded from my init.m2 file: ecoh, hf
load "points.m2" --- package that contains "randomPoints"

Cdeg=5 -- degree of the curve
Cgenus=5 -- geometric genus desired, <= (d-1)*(d-2)/2
nsing=((Cdeg-1)*(Cdeg-2))//2-Cgenus -- number of singular points. 
--(// is used to produce an int)

kk=ZZ/32003
R=kk[a,b,c] -- the plane
--make an equation f of a generic quintic singular at nsing points
i=randomPoints(R, nsing)
i2=saturate(i^2)
I2= gens i2
fC=ideal (I2*random(source I2, R^{-Cdeg})) 
fC
ideal a
hyp=(fC+ideal(a))
RC=R/fC -- the ring of the curve
Rhyp=R/hyp -- and of its hyperplane section
can=super(basis(Cdeg-3, i)) -- the adjoint linear series

--Now the smooth curve, canon emb by the quartics throught the 2-points
S=kk[vars(1..rank source can)] -- homog coord ring of canonical space
canmap = map(RC,S,substitute(can,vars RC)) -- the adjunction map
iC=kernel canmap
-- canonical ideal of C
betti iC
iC1=pushForward1(canmap, R^1/(fC*(R^1)))
betti iC1
---------------------------------











