This buffer is for notes you don't want to save, and for Lisp evaluation.
If you want to create a file, visit that file with C-x C-f,
then enter the text in that file's own buffer.
restart

S=QQ[x,y,z]
i=intersect(ideal(x,y),ideal(x-z,y),ideal(x-2*z,y), ideal(x,y-z))
transpose gens i

--xy           
--y2-yz        
--x3-3x2z+2xz2 

j=ideal(x^2,y^2,z^2)
I=intersect(i,j)
transpose gens I

--y2z-yz2      
--y3-yz2       
--xy2          
--x2y          
--x3-3x2z+2xz2 