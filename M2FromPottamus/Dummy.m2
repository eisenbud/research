newPackage(
       "Dummy",
       Version => "0.1",
       Date => "January 9, 2010",
       Authors => {
               {Name => "Baptiste Calmes"}
               },
       Headline => "Dummy package",
       DebuggingMode => true)

-- Put here the name of functions that should be visible to users
export{
mymethod,
a
}

-- Variables that can be modified by the user
exportMutable{
}

--package code

mymethod=method(Options => true)

mymethod(ZZ) := {a=>1} >> o -> (n) -> n*(o.a)

--documentation

beginDocumentation()
