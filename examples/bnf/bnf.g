{

(* header *)
let str_of_SYM sym = match sym with 
  | NT nt -> "parse_"^nt
  | TM tm -> "(term_to_parser \""^(String.escaped tm)^"\")"

let str_of_SYMS alt = "(" ^ (String.concat "**>" (List.map str_of_SYM alt)) ^ ")"

let str_of_ACT act = act

let str_of_SYMSACT (alt,act) = "("^ (str_of_SYMS alt) ^" >> ("^ ("" (* FIXME str_of_ACT act *)) ^"))"

let str_of_RHS rhs = "("^ (String.concat "|||" (List.map str_of_SYMSACT rhs)) ^")"

let str_of_RULE (nt,rhs) = (str_of_SYM (NT nt))^" = fun i -> (memo_check_and_upd_lctxt tbl_"^nt^" \""^nt^"\" (fun i -> unique ("^(str_of_RHS rhs)^" i)) i)"

let str_of_RULES rs = "let rec "^(String.concat "\n\n and " (List.map str_of_RULE rs))

}

START -> HG ?ws? "."    { fun ((h,rs),(_,_)) -> print_string (h^(str_of_RULES rs)); () }

HG -> RULES             { fun rs -> ("",rs) }
  | HEADER ?ws? RULES   { fun (h,(_,rs)) -> (h,rs) }

HEADER -> 
  "{" ?notcurlyr? "}"   { fun (_,(s,_)) -> content s } 

RULES -> RULE           { fun r -> [r] }
  | RULE ?ws? RULES     { fun (r,(_,rs)) -> r::rs }

RULE -> 
  SYM ?ws? "->" ?ws? RHS { fun (NT nt,(_,(_,(_,syms)))) -> (nt,syms) }

RHS -> SYMSACT          { fun syms -> [syms] } 
  | SYMSACT ?ws? "|" ?ws? RHS { fun (syms,(_,(bar_,(_,xs)))) -> syms::xs }

SYMSACT -> SYMS ?ws? ACT { fun (syms,(_,act)) -> (syms,act) }

SYMS -> SYM ?ws? SYMS   { fun (s,(_,ss)) -> s::ss }
  | SYM                 { fun s -> [s] }

ACT -> "{" ?notcurlyr? "}" { fun (_lt,(act,_gt)) -> (content act) }

SYM -> 
  '"' ?notdquote? '"'   { fun (_,(s,_)) -> TM("\"" ^ (content s) ^ "\"") }
  | "'" ?notsquote? "'" { fun (_,(s,_)) -> TM("\"" ^ (content s) ^ "\"") }
  | ?AZS?               { fun s -> NT (content s) }
  | "?" ?azAZs? "?"     { fun (_,(s,_)) -> TM("?" ^ (content s) ^ "?") }

.