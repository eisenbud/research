--Once I make a mistake with quotes, there seems
--no way to recover from the green output in the M2 window:

--To see the effect, start M2 in one emacs buffer,
--and execute the code below
--with f11 through the first line
-- 2+2
--then go back and
--put in the missing quotation mark after the word green,
--then execute all the code here, with f11. Emacs knows that something
--has changed, because it recolors the text after the quote
--is added. But the output in the other window stays green (on my system)
--even after a restart!

"This is a test
of green

2+2
"

restart
2+2


--Solution (from Grayson): type an extra quotation mark, followed by
--a carriage return.

