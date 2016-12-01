restart
needsPackage "Schubert2"
--viewHelp Schubert2
p=4
q=4

G = flagBundle({p,q},VariableNames=>{,"c"})
(S,Q) = G.Bundles
T = G.TangentBundle
L=exteriorPower(q,Q)
L' = (dual L)
chern(L' ++ T**L') 
integral chern(dim G,L' ++ T**L')

restart
needsPackage "Schubert2"

time map(QQ^7, QQ^7, (p,q) ->(
if p>q then 0 else (
G = flagBundle{p+1,q+1};
(S,Q) = G.Bundles;
T = G.TangentBundle;
L=exteriorPower(q+1,Q);
L' = (dual L);
integral chern(dim G, L' ++ T**L')
)))

--7x7 used 333.54 seconds; 10x10 didn't finish in 24 hours.