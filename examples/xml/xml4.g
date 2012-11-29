D -> ?notlt? ELT 
ELT -> S ELTA
ELTA -> ?notlt? ELTST
ELTST -> T | ELT ELTSTA 
ELTSTA -> ?notlt? ELTST

S -> "<" ?azAZ? ?notgt? ">"
T -> "<" "/" ?notgt? ">"


COMMENT -> "

  The idea is to parse lists of xml elts, separated by notlt, and
  terminated with an explicit T. This avoids the ambiguity when
  parsing a list.

  ELT is a single XML element.

  ELTST is a list of XML elements (initial character marks the start
  tag of the first element), separated by notlt, followed by a closing
  tag.

"
