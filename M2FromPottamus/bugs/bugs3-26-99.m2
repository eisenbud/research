HashTable{VERSION => 0.8.52                   }
                architecture => i586
                compile node name => geometry
                compile time => Mar  3 1999 08:31:10
                dumpdata => true
                factory => true
                factory version => 1.2c
                gc version => 4.13 alpha 3
                libfac version => 0.3.1
                mp => false
                operating system => Linux
                operating system release => 2.2.2

R=kk[a,b,c,d,e,s,t,MonomialOrder=>Eliminate 6]
i1=ideal(a*s+b*t, b*s+c*t, c+t)
substitute(i1, {t=>a})
substitute(i1, {t=>0})
--both give error messages
version
