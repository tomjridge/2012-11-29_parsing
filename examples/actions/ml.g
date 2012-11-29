{{

(* FIXME we don't need exact in the following - BAL is balanced, so parse_BRACKET must parse the whole thing *)

let exact p s = 
  let xs = p s in
  List.filter (fun (_,s_rem) -> len s_rem = 0) xs

}}

START -> "`" ?epsws? EXP ?epsws? "`"                             {{ fun (_,(_,(i,(_,_)))) -> let _ = print_string ("Parsed an exp\n"^i^"\n\n") in i }}

EXP -> 
    ATEXP                                                        {{ fun i -> i }}
  | EXP ?epsws? INFIX ?epsws? EXP                                {{ fun (e1,(_,(i,(_,e2)))) -> e1^" "^i^" "^e2 }} 
  | FNARGS                                                       {{ fun ss -> (String.concat " " ss) }}
  | "case" ?ws? EXP ?ws? "of" ?ws? CASES                         {{ fun (_,(_,(e,(_,(_,(_,cs)))))) -> ("caseof("^e^","^(String.concat "||" cs)^")") }}
  | "if" ?ws? EXP ?ws? "then" ?ws? EXP ?ws? "else" ?ws? EXP      {{ fun (_,(_,(e1,(_,(_,(_,(e2,(_,(_,(_,(e3))))))))))) -> ("ifthenelse("^e1^","^e2^","^e3^")") }}
  | "let" ?ws? EXP ?ws? "in" ?ws? EXP                            {{ fun (_,(_,(e1,(_,(_,(_,e2)))))) -> "let "^e1^" in "^e2 }}
  | "\" ?epsws? EXP ?epsws? "." ?epsws? EXP                      {{ fun (_,(_,(e1,(_,(_,(_,e2)))))) -> "\\ "^e1^" . "^e2 }}
  | EXP ":" TYPE                                                 {{ fun (e,(_,t)) -> e^":"^t }} 


TYPE -> ?ident?                                                  {{ fun s -> content s }}
  | "'" ?ident?                                                  {{ fun (_,s2) -> "'" ^ (content s2) }}
  | TYPE "->" TYPE                                               {{ fun (t1,(_,t2)) -> t1^"->"^t2 }}
  | TYPE ?ws? ?ident?                                            {{ fun (t,(_,i)) -> t^" "^(content i) }}

ATEXP -> 
    BAL                                                          {{ fun s ->    
                                                                     let (r,_)::_ = (exact parse_BRACKET (toinput s)) in r }}

  | ?ident?                                                      {{ fun s -> content s }}
  | '"' ?notdquote? '"'                                          {{ fun (_,(s,_)) -> ("\"" ^ (content s) ^ "\"") }} 
  | "[" ?epsws? EXPLIST ?epsws? "]"                              {{ fun (_,(_,(ss,(_,_)))) -> "[" ^ (String.concat ";" ss) ^ "]" }}
  | '"' "[]" '"'                                                 {{ fun _ -> "\"[]\"" }}
  | '"' "::" '"'                                                 {{ fun _ -> "\"::\"" (* not really an infix *) }}
  | RECORD                                                       {{ fun i -> i }}

BRACKET -> 
    "(" ")"                                                      {{ fun _ -> "()" }}
  | "(*" ?all?                                                   {{ fun (c1,c2) -> content(dest_Some (concatenate_two c1 c2)) (* FIXME comments should be treated as ws *) }}
  | "(" ?epsws? EXP ?epsws? ")"                                  {{ fun (s1,(s2,(e,(s4,s5)))) -> "("^e^")" }}
  | "(" EXP "," ?epsws? EXP ")"                                  {{ fun (_,(e1,(_,(_,(e2,_))))) -> ("("^e1^","^e2^")") }}
  | "(" EXP "," ?epsws? EXP "," ?epsws? EXP ")"                  {{ fun (_,(e1,(_,(_,(e2,(_,(_,(e3,_)))))))) -> ("("^e1^","^e2^","^e3^")") }}

BAL -> "(" KET                                                   {{ fun (s1,s2) -> dest_Some (concatenate_two s1 s2) }}
KET -> ?notbracket? ")"                                          {{ fun (s1,s2) -> dest_Some (concatenate_two s1 s2) }}
  | ?notbracket? BAL KET                                         {{ fun (s1,(s2,s3)) -> dest_Some (concatenate_list [s1;s2;s3]) }}

EXPLIST ->
  ""                                                             {{ fun _ -> [] }}
  | EXP                                                          {{ fun e -> [e] }}
  | EXP ";" EXPLIST                                              {{ fun (e,(_,es)) -> e::es }} 

INFIX -> "="                                                     {{ fun s -> content s }}
  | "++"                                                         {{ fun s -> content s }}
  | "::"                                                         {{ fun s -> content s (* FIXME not an infix ?*) }} 

FNARGS -> ATEXP ?epsws? ATEXP                                    {{ fun (e1,(_,e2)) -> [e1; e2] }}
  | ATEXP ?epsws? FNARGS                                         {{ fun (s,(_,ss)) -> ( s)::ss }}

CASES -> CASE                                                    {{ fun s -> [s] }}
  | CASE ?ws? "||" ?ws? CASES                                    {{ fun (c,(_,(_,(_,cs)))) -> c::cs }}


CASE -> EXP ?ws? "->" ?ws? EXP                                   {{ fun (e1,(_,(_,(_,e2)))) -> "("^e1^"->"^e2^")" }}
  | "_" ?ws? "->" ?ws? EXP                                       {{ fun (_,(_,(_,(_,e)))) -> "(_->"^e^")" }}


RECORD ->
    "<|" ?epsws? FIELDS ?epsws? "|>"                             {{ fun (_,(_,(fs,(_,_)))) -> "<| "^(String.concat "; " fs)^" |>" }}

FIELDS -> 
    ""                                                           {{ fun _ -> [] }}
  | FIELD                                                        {{ fun f -> [f] }}
  | FIELD ?epsws? ";" ?epsws? FIELDS                             {{ fun (f,(_,(_,(_,fs)))) -> f::fs }}

FIELD -> 
    ?ident? ?epsws? ":=" ?epsws? EXP                             {{ fun (f,(_,(_,(_,e)))) -> ((content f)^" := "^e) }}


(* 

  | "::"                                                         {{ fun s -> content s ( * not an infix * ) }}
*)
