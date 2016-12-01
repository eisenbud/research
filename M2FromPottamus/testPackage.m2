uninstallPackage "RandomIdeal"
restart
installPackage  "RandomIdeal"
viewHelp "RandomIdeal"
viewHelp RandomIdeal


viewHelp randomMonomial
viewHelp (randomMonomial, ZZ, Ring)
viewHelp randomMonomialIdeal
viewHelp randomSquareFreeMonomialIdeal
viewHelp squareFree
viewHelp regSeq
viewHelp randomIdeal
viewHelp randomBinomialIdeal
viewHelp randomPureBinomialIdeal

kk=ZZ/101
S=kk[a,b]
B=vars S
(first entries B)_0
viewHelp random
ideal apply (flatten entries vars S, p -> p^2)

--compare the speed -- "basis" is much faster.
restart
S=kk[vars (0..10)]
mm=ideal vars S
time for d from 1 to 15 do basis(d, S^1)
time for d from 1 to 15 do flatten entries gens mm^d

