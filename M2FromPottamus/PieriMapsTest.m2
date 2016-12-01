viewHelp pieri
viewHelp PieriMaps
pieri({4},{2},QQ^4)-- fails with an index out of bounds msg.
pieri({4},{1},QQ^2) -- OK
pieri({4},{0},QQ^2) -- fails with index out of bounds
pieri({4},{1,1},QQ^2) -- OK

pieri({1,1},{0},QQ^2) --Produces the zero map S^1 --> S^1. I don't understand this.
pieri({1,1},{1,1},QQ^2) --fails with "array index out of bounds. 
pieri({1,1},{2,1},QQ^2) -- should be the map $\Lambda^2(QQ^2) \to Sym_2(QQ^2)$, which is 
--the zero map from S^1 to S^3, not S^1 to S^1. I think this is wrong.
pieri({1,1,1},{3}, QQ^3) -- OK
pieri({1,1,1},{2}, QQ^3) --fails with "array index out of bounds. 

