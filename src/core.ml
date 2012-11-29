
(*
# Graph of dependencies in current file

The following shows the dependencies present in this file.

        core (library) ----+
        |                  |   
        coretermnonterm    (external term/nonterm)
        |                  |
        core --------------+
        |
        +---+  
        |   |
        X   parseg
            |
            cl ----------------------+
            |       |        |       |
            main_cf main_cft main_pt main_simp

# Core
## Precore,postcore - functor defn

*)


(*
## Library
*)


type ('a,'b) sum = Inl of 'a | Inr of 'b

(* FIXME change names of predefined combinators to reflect use of not_epsilon (i.e. default is epsilon) *)

let rec itlist f l b =
  match l with
    [] -> b
  | (h::t) -> f h (itlist f t b);;

let rec mem x lis =
  match lis with
    [] -> false
  | (h::t) -> Pervasives.compare x h = 0 or mem x t;;

let insert x l =
  if mem x l then l else x::l;;

let union l1 l2 = itlist insert l1 l2;;

let unions l = itlist union l [];;


let ($) f g x = f(g x)

let read_file_as_string fn = 
  let f = open_in fn in
  let s = ref "" in
  let _ = try (while(true) do s := (!s) ^ (input_line f) ^ "\n" done) with _ -> () in
  let _ = close_in f in
  !s

(* our contexts are sorted; we need insertion into a sorted list; we expect no duplicates  *)
let rec myinsert cmp elt lst = match lst with
  [] -> [elt]
| head :: tail -> let r = cmp elt head in if r < 0  then elt :: lst else (
  if r = 0 then failwith "myinsert" else head :: myinsert cmp elt tail)

(* get a list with no duplicates; very inefficient *)
let unique_f res e = if List.mem e res then res else e::res

let unique = fun e -> List.fold_left unique_f [] e

let dest_Some x = match x with Some y -> y | _ -> failwith "dest_Some"



(*
## Types
*)

type term = string

type nonterm = string

let string_of_tm tm = tm

let string_of_nt nt = nt

let eps = "\"\""


type substring = string * int * int

type symbol = NT of nonterm | TM of term

type rhs = (symbol list) list

type parse_rule = nonterm * rhs

type grammar = parse_rule list

type parse_tree = NODE of nonterm * parse_tree list | LF of term * substring

(* local_context invariant: each entry has the same substring (ie the
most restrictive substring); entries are sorted on nonterm *)

type lc_substring = int * int

type local_context = (nonterm * lc_substring) list 

type ty_input = { lc1 : local_context; sb1 : substring }

type 'a parser = ty_input -> ('a * substring) list

type ty_p_of_tm = term -> substring parser

(* memoization *)
type key = (nonterm * local_context * lc_substring)

type ty_compact_form = (nonterm * lc_substring) list

(* compact forms *)
type parsed_sym = (symbol * lc_substring)
type parse_result = 
  | PNODE of (nonterm * lc_substring) * (parsed_sym list)
  | PLEAF of (term * lc_substring)

(* grammar_to_parser parameterization *)

type 'a g2p_params = {
  p_of_tm3: term -> 'a parser;
  then_list3: nonterm -> 'a parser list -> 'a parser;
  check_and_upd_lctxt3: nonterm -> 'a parser -> 'a parser;
  unique3: 'a parser -> 'a parser;
}


(*
## Substrings
*)

let string (s,l,h) = s

let (low,high,len) = (
  (fun (s,l,h) -> l), 
  (fun (s,l,h) -> h), 
  (fun (s,l,h) -> h-l))

let full s = (s,0,String.length s)

let inc_low n (s,l,h) = (s,l+n,h)
let dec_high n (s,l,h) = (s,l,h-n)
let inc_high n (s,l,h) = (s,l,h+n)

let content s = 
  String.sub (string s) (low s) (len s)

let concatenate_two s1 s2 = 
  if (string s1 = string s2) && (high s1 = low s2) then
    Some (string s1, low s1, high s2)
  else
    None

let rec concatenate_list ss = match ss with 
  [] -> None
| s1::ss -> (match ss with
    [] -> Some s1
  | _ -> (match concatenate_list ss with 
      None -> None
  |   Some s2 -> concatenate_two s1 s2))



(*
## Common functions
*)

let string_of_symbol sym = match sym with | NT nt -> "NT("^(string_of_nt nt)^")" | TM tm -> "TM("^(string_of_tm tm)^")"

let string_of_substring (s,l,h) = "("^s^","^(string_of_int l)^","^(string_of_int h)^")"

let lc_substring_of (s,l,h) = (l,h)

let is_NT s = match s with NT _ -> true | _ -> false

let dest_NT sym = match sym with NT x -> x | _ -> failwith "dest_NT"

let is_TM sym = match sym with TM _ -> true | _ -> false

let dest_TM sym = match sym with NT _ -> failwith "dest_TM" | TM tm -> tm

let eps = TM(eps) (* fix one particular terminal for eps *)

let toinput s = { lc1=[]; sb1=s } 

let (_:substring -> ty_input) = toinput

let substr i = i.sb1

let (_:ty_input -> substring) = substr

let lift f i = { i with sb1=(f i.sb1) }

let (_: (substring -> substring) -> (ty_input -> ty_input)) = lift

let syms_of_rhs rhs = unions rhs

let syms_of_parse_rule (nt,rhs) = insert (NT(nt)) (syms_of_rhs rhs)

let syms_of_grammar g = unions (List.map syms_of_parse_rule g)



(*
## Combinators

It is worth noting that nothing in the following definitions depends on the notion of context. Context comes later, and is modularly combined with the following.

*)

(* 'a parser -> 'b parser -> ('a * 'b) parser *)
(*
let ( **> ) p1 p2 = fun i ->
  let f (e1,s1) = 
    List.map (fun (e2,s2) -> ((e1,e2),s2)) (p2 { gc=i.gc; lc1=i.lc1; sb=s1 }) 
  in
  (List.concat $ (List.map f) $ p1) i
    
let (_:'a parser -> 'b parser -> ('a * 'b) parser) = ( **> )
*)

(* 'a parser -> ('a -> 'b) -> 'b parser *)
let (>>) p f = 
  (List.map (fun (e,s) -> (f e, s))) $ p

(* 'a parser -> 'a parser -> 'a parser *)
let (|||) p1 p2 = fun s -> List.append (p1 s) (p2 s)

(* a version of the combinator that ignores duplicate entries FIXME *)
let ( **> ) p1 p2 = fun i ->
  let f (e1,s1) = 
    List.map (fun (e2,s2) -> ((e1,e2),s2)) (p2 { lc1=i.lc1; sb1=s1 }) 
  in
  ((List.concat $ (List.map f) $ p1) i)

let (_:'a parser -> 'b parser -> ('a * 'b) parser) = ( **> )


let always = fun i -> [([],substr i)]

let never = fun i -> []


let rec then_list ps = match ps with 
| [] -> always
| p::ps -> (p **> (then_list ps)) 
    >> (fun (x,xs) -> (x::xs))

let then_list2 nt = fun ps -> then_list ps >> (fun xs -> NODE(nt,xs))


let rec or_list ps = match ps with 
| [] -> never
| p::ps -> (p ||| (or_list ps))


(* 'a parser -> 'a parser *)
let ignr_last p = fun i -> 
  if len (substr i) = 0 then [] else
  let inc_high (e,s) = (e,inc_high 1 s) in 
  ((List.map inc_high) $ p $ (lift (dec_high 1))) i

let (_:'a parser -> 'a parser) = ignr_last


let not_epsilon p = fun i ->
  List.filter (fun (v,_) -> not (len v = 0)) (p i)

let (_:substring parser -> substring parser) = not_epsilon

let noteps p = fun i -> 
  List.filter (fun (_,srem) -> srem <> substr i) (p i)

let (_:'a parser -> 'a parser) = noteps

(* string -> substring parser *)
let a lit = fun i ->
  let n = String.length lit in
  let s = substr i in
  if 
    (n <= len s) 
    && (String.sub (string s) (low s) n = lit) 
  then
    let (s1,l,h) = s in
    let s2 = (s1,l,l+n) in
    [(s2,inc_low n s)]
  else
    []

let (_:substring parser) = (a "1")

let rec listof item sep = fun i -> 
  (((a "") >> (fun _ -> []))
   ||| (item >> (fun x -> [x]))
   ||| ((item **> sep **> (listof item sep)) >> (fun (x,(_,xs)) -> x::xs))) i

let rec star item = fun i -> 
  (((a "") >> (fun _ -> []))
   ||| ((item **> (star item)) >> (fun (x,xs) -> x::xs))) i

let rec itern item n = (match n with 
  | 0 -> ((a "") >> (fun _ -> []))
  | _ -> ((item **> (itern item (n-1))) >> (fun (x,xs) -> x::xs)) )

let just a = (always >> (fun _ -> a))

let braskets bra item ket = fun i ->
  let rs1 = ((star bra) i) in
  (* rs1 is a list of results, each result is a list of the bra results *)
  let f (e1,s1) = 
    let p = (item **> (itern ket (List.length e1))) >> (fun (x,xs) -> (e1,x,xs)) in
    p { lc1=i.lc1; sb1=s1 }
  in
  List.concat (List.map f rs1)
  


(*
## Basic parsers
*)



(* FIXME change this to take an underlying parser *)
let until_a lit = fun i -> 
  let llit = String.length lit in
  let s = substr i in
  let rec f1 n =
    if 
      n+llit <= len s
      && (String.sub (string s) ((low s)+n) llit) = lit
    then
      let (s1,l,h) = s in
      let s2 = (s1,l,l+n) in
      [(s2,inc_low n s)]
    else if 
        n+llit <= len s
    then 
      f1 (n+1)
    else
      let (s1,l,h) = s in
      [(s,(s1,h,h))]
  in
  f1 0
  

(* pred is a function from a string of length 1 to a bool *)
let parse1 pred = fun i -> 
  let s = substr i in
  if (1 <= len s && pred (String.sub (string s) (low s) 1)) then
    [((string s, low s, 1+low s),inc_low 1 s)]
  else 
    []

let parse_azAZ = 
  let pred = fun c ->
    ((String.compare "A" c <= 0) && (String.compare c "Z" <= 0))
    || ((String.compare "a" c <= 0) && (String.compare c "z" <= 0))
  in
  parse1 pred

let (_:substring parser) = parse_azAZ



let parse_EOF = fun i -> (
  if (low i.sb1 = high i.sb1) && (high i.sb1 = String.length (string i.sb1)) then 
    (a "") i 
  else 
    never i)

let a1 = (a "1") >> (fun _ -> 1)

(* can return eps; FIXME this is incredibly dangerous, and breaks wf of terminal parsers *)
let parse_while pred = fun i ->
  let s = substr i in
  let rec f = fun n -> 
    if n = len s then len s else
    let c = String.sub (string s) ((low s)+n) 1 in
    if pred c then f (n+1) else n 
  in
  let n = f 0 in
  let r = (string s, low s, (low s)+n) in
  [(r,inc_low n s)]

let (_:(string -> bool) -> substring parser) = parse_while

let parse_AZS = 
  let pred c = 
    (String.compare "A" c <= 0) 
    && (String.compare c "Z" <= 0) 
  in
  not_epsilon (parse_while pred)

let parse_ws = not_epsilon (parse_while (fun s -> s = " " || s = "\n"))

let parse_epsws = (parse_while (fun s -> s = " " || s = "\n"))

let parse_newline = a "\n"

let parse_azAZs = 
  let pred = fun c ->
    ((String.compare "A" c <= 0) && (String.compare c "Z" <= 0))
    || ((String.compare "a" c <= 0) && (String.compare c "z" <= 0))
  in
  not_epsilon (parse_while pred)

let parse_notdquote = 
  parse_while (fun c -> not (c = "\""))

let parse_notsquote = 
  parse_while (fun c -> not (c = "'"))

let parse_notlt = 
  parse_while (fun c -> not (c = "<"))

let parse_notgt = 
  parse_while (fun c -> not (c = ">"))

let parse_notltgt = 
  parse_while (fun c -> not ((c = "<") || (c = ">")))

let parse_notbracket = 
  parse_while (fun c -> not ((c = "(") || (c = ")")))

let parse_notws =
  parse_while (fun c -> not (c = " "))

let parse_notcurlyr = parse_while (fun c -> not (c = "}"))

let parse_all = 
  parse_while (fun c -> true)

let parse_num = 
  let pred = fun c ->
    (String.compare "0" c <= 0) && (String.compare c "9" <= 0)
  in
  not_epsilon (parse_while pred)

let parse_ident = 
  let pred = fun c -> 
    ((String.compare "A" c <= 0) && (String.compare c "Z" <= 0))
    || ((String.compare "a" c <= 0) && (String.compare c "z" <= 0))
    || (String.compare "0" c <= 0) && (String.compare c "9" <= 0)
    || (c = "_") || (c = "'")
  in
  not_epsilon (parse_while pred)

(* parsers for command line parsing *)

(* we use "\x00" as an arg separator - assumes this char does not appear on the cl *)
let parse_FLAG = ((a "-") **> parse_azAZs) >> (fun (_,s) -> "-"^(content s))


(* first char should not be a - *)
let parse_ARG = 
  let parse_not_minus = parse1 (fun c -> c <> "-") in
  (parse_not_minus **> parse_while (fun s -> s <> "\x00")) >> (fun (s1,s2) -> ((content s1)^(content s2)))

let parse_FLARGS = 
  let sep = a "\x00" in
  (parse_FLAG **> sep **> (listof parse_ARG sep)) >> (fun (f,(_,xs)) -> (f,xs)) 

let term_to_parser s = 
  match s with
  | "?AZS?" -> parse_AZS 
  | "?all?"   -> parse_all
  | "?azAZ?" -> parse_azAZ 
  | "?azAZs?" -> parse_azAZs 
  | "?EOF?" -> parse_EOF
  | "?epsws?" -> parse_epsws 
  | "?ident?" -> parse_ident
  | "?newline?" -> parse_newline
  | "?notbracket?" -> parse_notbracket
  | "?notcurlyr?" -> parse_notcurlyr
  | "?notdquote?" -> parse_notdquote 
  | "?notgt?" -> parse_notgt
  | "?notlt?" -> parse_notlt
  | "?notltgt?" -> parse_notltgt
  | "?notsquote?" -> parse_notsquote 
  | "?num?" -> parse_num
  | "?ws?" -> parse_ws 
  | "\"\"" -> a ""
  | _ -> ( (* interpret as a literal *)
      if String.length s < 2 then failwith ("term_to_parser: "^s) 
      else 
	let _ = () (* print_string ("term_to_parser: treating "^s^" as a literal\n") *) in
	(a (String.sub s 1 (String.length s - 2))))


let (_:term -> substring parser) = term_to_parser



(*
## Context
*)

(* debug version; assumes s1 = s2 (since the only part of the context that matters is...) *)
let lc_cmp (nt1,(l1,h1)) (nt2,(l2,h2)) = 
  if (l1,h1) <> (l2,h2) then failwith "lc_cmp" else Pervasives.compare nt1 nt2

(* remember what NT is called on what input *)
(* nonterm -> 'a parser -> 'a parser *)
let update_lctxt nt p = fun i -> 
  let lc = List.filter (fun (nt,(l,h)) -> (l,h) = lc_substring_of i.sb1) i.lc1 in 
  p { i with lc1=(myinsert lc_cmp (nt,lc_substring_of i.sb1) lc) }

let (_:nonterm -> 'a parser -> 'a parser) = update_lctxt

(* nonterm -> 'a parser -> 'a parser *)
let check_and_upd_lctxt nt p = fun i ->
  let should_trim = List.exists ((=) (nt,lc_substring_of i.sb1)) i.lc1 in 
  if should_trim && (len i.sb1 = 0) then 
    []
  else if should_trim then
    (ignr_last (update_lctxt nt p)) i
  else 
    (update_lctxt nt p) i

let (_:nonterm -> 'a parser -> 'a parser) = check_and_upd_lctxt


(* simple memoization *)

(* (key,('a * substring)list) Hashtbl.t -> nonterm -> 'a parser -> 'a parser *)
let memo_check_and_upd_lctxt tbl nt p i = 
  let i = { i with lc1=List.filter (fun (nt,s) -> s = lc_substring_of i.sb1) i.lc1} in
  (* first look in the global memo table *)
  let k = (nt,i.lc1,lc_substring_of i.sb1) in
  if Hashtbl.mem tbl k then Hashtbl.find tbl k else 
  (* if not already present then proceed as normal, but remember the value *)
  let v = 
    let should_trim = List.exists ((=) (nt,lc_substring_of i.sb1)) i.lc1 in 
    if should_trim && (len i.sb1 = 0) then 
      []
    else if should_trim then
      (ignr_last (update_lctxt nt p)) i
    else 
      (update_lctxt nt p) i
  in
  let _ = Hashtbl.add tbl k v in
  v

let (_:(key,('a * substring)list) Hashtbl.t -> nonterm -> 'a parser -> 'a parser) = 
  memo_check_and_upd_lctxt

;;

(*
## `grammar_to_parser`

This is the plain version that appears in the paper and the HOL4 formalization.

*)


let rec grammar_to_parser p_of_tm g sym i = match sym with 
  TM tm -> ((p_of_tm tm) >> (fun v -> LF(tm,v))) i | NT nt -> 
  let rules = List.filter (fun (nt',rhs) -> nt' = nt) g in
  let alts1 = (List.concat $ (List.map snd)) rules in
  let alts2 = List.map (List.map (grammar_to_parser p_of_tm g)) alts1 in
  let p = or_list (List.map (then_list2 nt) alts2) in
  check_and_upd_lctxt nt p i

let (_: (term -> substring parser) -> grammar -> symbol -> parse_tree parser) = grammar_to_parser

let g2p_params p_of_tm = {
  p_of_tm3=(fun tm -> (p_of_tm tm) >> (fun v -> LF(tm,v)));
  then_list3=(fun nt -> then_list2 nt);
  check_and_upd_lctxt3=(fun nt -> check_and_upd_lctxt nt);
  unique3=(fun p -> p);
}

let rec g2p params g sym i = (match sym with 
  TM tm -> params.p_of_tm3 tm i | NT nt -> 
  let rules = List.filter (fun (nt',rhs) -> nt' = nt) g in
  let alts1 = (List.concat $ (List.map snd)) rules in
  let alts2 = List.map (List.map (g2p params g)) alts1 in
  let p = or_list (List.map (params.then_list3 nt) alts2) in
  let q = params.unique3 p in
  params.check_and_upd_lctxt3 nt q i)

(* version via parameterization *)
let grammar_to_parser p_of_tm = g2p (g2p_params p_of_tm)

;;


(*
## Parse a grammar file
*)


let tm_of_lit lit = TM("\"" ^ lit ^ "\"")

let parse_comm = fun i -> ((a "(*") **> until_a "*)" **> (a "*)")) i

(* FIXME only one comment in ws? *)
let parse_wscomm = 
  ((parse_ws >> (fun _ -> ""))
   ||| ((parse_ws **> parse_comm **> parse_ws) >> (fun _ -> "")))

let rec parse_GRAMMAR = fun i -> 
  ((parse_RULES **> parse_wscomm **> parse_EOF) >> (fun (rs,(_,_)) -> rs)) i

and parse_RULES = fun i -> (listof parse_RULE parse_wscomm) i

and parse_RULE = fun i ->
  ((parse_SYM **> parse_wscomm **> (a "->") **> parse_wscomm **> parse_SYMSLIST) >> (fun (nt,(_,(_,(_,syms)))) -> (dest_NT nt,syms))) i

and parse_SYMSLIST = fun i -> 
  (listof parse_SYMS (parse_wscomm **> (a "|") **> parse_wscomm)) i

(* N.B. we do not allow empty lists here *)
and parse_SYMS = fun i ->
  (noteps (listof parse_SYM parse_wscomm))  i

and parse_SYM = fun i ->
  ((((a "\"") **> parse_notdquote **> (a "\"")) >> (fun (_,(s,_)) -> tm_of_lit (content s)))
  ||| (((a "'") **> parse_notsquote **> (a "'")) >> (fun (_,(s,_)) -> tm_of_lit (content s)))
  ||| (parse_AZS >> (fun s -> NT (content s)))
  ||| (((a "?") **> parse_azAZs **> (a "?")) >> (fun (_,(s,_)) -> TM("?" ^ (content s) ^ "?"))))
    i

(* FIXME version with actions *)

let rec parse_GRAMMAR_WITH_ACTIONS = fun i -> 
  ((parse_HG **> parse_wscomm **> parse_EOF) >> (fun (h,_) -> h)) i

and parse_HG = fun i -> 
  (parse_RULES >> (fun rs -> ("",rs))
  ||| ((parse_HEADER **> parse_wscomm **> parse_RULES) >> (fun (h,(_,rs)) -> (h,rs)))) i

and parse_HEADER = fun i -> parse_CODE i

and parse_RULES = fun i -> (listof parse_RULE parse_wscomm) i

and parse_RULE = fun i ->
  ((parse_SYM **> parse_wscomm **> (a "->") **> parse_wscomm **> parse_RHS) >> (fun (NT nt,(_,(_,(_,syms)))) -> (nt,syms))) i

and parse_RHS = fun i ->
  (listof parse_SYMSACT (parse_wscomm **> (a "|") **> parse_wscomm)) i

and parse_SYMSACT = fun i -> 
  ((parse_SYMS **> parse_wscomm **> parse_ACT) >> (fun (syms,(_,act)) -> (syms,act))) i

and parse_ACT = fun i -> parse_CODE i

and parse_CODE = fun i -> 
  (((a "{{") **> until_a "}}" **> (a "}}")) >> (fun (_lt,(act,_gt)) -> (content act))) i

;;

(*
# Entry points (main functions)
## cl - command line parsing
*)


(*
*)


(*
*)


(*
*)

