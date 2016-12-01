loadPackage "BoijSoederberg"
viewHelp "BoijSoederberg"

--Conjecture: the multiplicity of modules formed from the pure resolutions
--constructed in my paper with Schreyer depend ONLY on the jumps in the degrees,
--and not on their placement OR their order.

B0=pureCharFree({0,3,4,5})
B=pureBettiDiagram {0,3,4,5}
peek B

degree B

deg = L ->(
B0 := pureCharFree L;
B := pureBettiDiagram L;
(B0/B#(0,{0},0))*degree B)

makeLists = (e1,e2,n)->(
     L := {};
     for i from 1 to n do
         for j from i to n do
    L = L | {deepSplice toList(0..i,i+e1..j+e1,j+e1+e2..n+e1+e2)};
    L)
L=makeLists(2,5,4)
for i from 0 to #L-1 do 
      print deg L_i
deg{0,2,4,6,7,8,9}==deg{0,1,3,4,6,7,9}
deg{0,1,3,4,9}==deg{0,5,7,8,9}


deg(L_0)
pureBettiDiagram(L_0)	  

deg{0,3,4,}     
deg{0,1,4,6}
deg{0,1,2,5}

