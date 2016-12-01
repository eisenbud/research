in the newPackage html page theres a repeated sentence (first para of
     the "Description" section.
     
The "creating a package page" (accessed from "package") doesn't mention
simpleDoc

Neither does the "document" page, nor the "writing documentation" page.

The "beginDocumentation()" page fortunately DOES mention simpleDoc

when fixing the documentation pages of my package, it seemed not enough
to do "uninstallPackage"; I also had to restart in between installs as well.

------------

Using simpleDoc, I had some troubles:

The spacing is very particular, and I didn't find the documentation
and examples clear enough. I think the sentence in the documentation of
simpleDoc, which is

The text is divided into sections, each of which begins with a keyword alone on a line;
 the keywords must all be indented to the same level, and everything else must be further indented.
 
is an incomplete specification. (Don't at least some of the subsequence indentations have to
line up? Of course I may have had multiple errors, but it took me a LOT of tries to
get things to compile correctly.)

It also wasn't clear what could go into the Key line (several
     lines of text, or whether it needed to have quotes etc
In fact, the documentation specifies that the node for the whole pkg,
in my case RandomIdeal, should have quotes; but when I added quotes,
viewHelp couldn't find the node.

Even when everything compiled, the links created in the web pages
didn't work.

