D -> ?notlt? E
E -> S ES T 
ES -> ?notlt? | ?notlt? E ES
S -> "<" ?azAZ? ?notgt? ">"
T -> "<" "/" ?notgt? ">"

COMMENT -> "

  A naive attempt at parsing xml; ES is a possibly empty list of xml
elts, separated by notlt

"
