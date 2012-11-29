# Simple, functional, sound and complete parsing for all context-free grammars


This is a collection of resources to accompany the paper submission to
CPP2011. A big thanks to Max Bolingbroke for everything related to
Haskell and Happy.


  * The paper is [here](http://www.tom-ridge.com/doc/ridge11parsing-cpp.pdf).
  
  * [doc/parsing.html](doc/parsing.html) - documentation for the OCaml code
  
  * [src/README.html](src/README.html) - OCaml code for the parser

  * [examples](examples) - example grammars and inputs

  * [hol](hol) - the HOL4 proof script
  
  * A bundle of all the files (including the Happy test harness) is
    [here](../parsing.tar.gz)


## Quick start

With OCaml installed, compile `src/main.ml`, and test it on an
example grammar.

    ocamlopt -o a.out src/main.ml
    ./a.out -g examples/E_EEE/E_EEE5.g -f examples/E_EEE/10.txt
    
