
restart
kk=ZZ/101
RU=kk[x,y]
i=(ideal vars RU)^2
regularity module i
regularity i

j=i^0
regularity module j -- this is right, gives 0
regularity j  --- 1 is the wrong answer!
