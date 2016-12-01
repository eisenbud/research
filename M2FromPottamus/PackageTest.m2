newPackage(
        "PackageTest",
        Version => "0.1", 
        Date => "",
        Authors => {{Name => "", 
                  Email => "", 
                  HomePage => ""}},
        Headline => "",
        DebuggingMode => true
        )

export {test}

test = a -> a

beginDocumentation()

doc ///
Key
  test
Headline
  test of
Description
 Text
 Example
Caveat
SeeAlso
///

doc///
Key 
  test
Headline
  "Test of Package making"
Usage
  a = test b 
Inputs
  b:ZZ
    can be really big
Outputs
  a:ZZ
Consequences
Description
 Text
  Hello
Caveat
SeeAlso
///


TEST ///
-- test code and assertions here
-- may have as many TEST sections as needed
///

end
uninstallPackage "PackageTest"
installPackage "PackageTest"
