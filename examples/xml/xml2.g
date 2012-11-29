D -> ?notlt? E 
E -> S F 
F -> ?notlt? T | ?notlt? E F
S -> "<" ?azAZs? ?notgt? ">"
T -> "<" "/" ?notgt? ">"

COMMENT -> "As xml.g, but attempting to factor out some rules"
