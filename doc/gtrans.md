# GTrans - grammar transformation 

We transform any context free grammar to an equivalent form, which
prunes some parse trees.

One of the optimizations is to split `E` into `E+` and `E-`, where `E-
-> eps` if E caneps. This avoids repeated unfolding of a parse tree
which eventually parses eps.

The other optimization is that each `E+` rule starts with a non-eps
terminal, and references only other `F+` nonterms. Actually, does this
second bit really matter? Probably not, see negligble performance
difference between `E_EEE5.g` and `E_EEE6.g`. The point is to have
something in the plus that cannot eps.

    E -> E E E
    
becomes
 
    E+ -> E+ E E | E- E E

The other thing is to consider whether the plus really contributes -
`E_EEE7.g` clearly is much slower, as is `E_EEE8.g`. Rather than a
top-down parse, we are moving towards a while parse, and this may be
making everything quicker.


      
 

The general structure of this development is:
    
  * `min_elim` - eliminate a `min_fsm` to a `minre`

  * `min_fsm_of_grammar1` - convert a `grammar1` to a `min_fsm`

First we introduce our types for terminals and nonterminals.



~~~{.ocaml}

(* FIXME instead of the following, open TagTMNT *)

type term = string
type tag = None1 | Plus1 | Minus1
type nonterm = string * tag

let string_of_tag t = (match t with 
  | None1 -> "0"
  | Plus1 -> "+"
  | Minus1 -> "-")

let string_of_nt (s,t) = s^"("^(string_of_tag t)^")"

let string_of_tm tm = tm

(*
let mk_Plus1 sym = (match sym with 
  | NT(nt,t) -> (NT(nt,Plus1))
  | _ -> sym)
*)

~~~

## Libraries

~~~{.ocaml}
 #cd "/tmp/l/general/research/parsing/src";;
 #use "hol_light_lib.ml";;
 #use "fmap.ml";;
 #use "graph.ml";;
 
(* #use "corenotermnonterm.ml";; *)

open TagTMNT;;
open TagCore;;

let break p xs = 
  let rec b p xs ys = match ys with [] -> (xs,ys)
    | y::ys -> if p y then b p (xs@[y]) ys else (xs,y::ys)
  in
  b p [] xs

let is_Some x = (match x with Some _ -> true | _ -> false)


~~~

## Types

Some basic types associated with `min_fsm`.


~~~{.ocaml}

(* this type is the minimal type for our particular version of elimination *)
type 'a minre = ATOM2 of 'a | SEQPLUS2 of 'a minre * 'a minre list option * 'a minre

(* 'a linre list is a canonical form of the above *)
type 'a linre = ATOM3 of 'a | PLUS3 of ('a linre list) list

type min_edge = { src5: symbol; dst5: symbol; lbl5: symbol list minre }

type min_fsm = (symbol,min_edge) graph1

~~~


~~~{.ocaml}
type edge1 = { src3:symbol; dst3:symbol; lbl3: symbol list }


~~~

A simple form of grammar, but no less expressive.


~~~{.ocaml}
type rhs1 = rhs

type parse_rule1 = parse_rule

type grammar1 = parse_rule1 list

~~~


A more complex form of grammar; a grammar in this form can be
transformed to a simple grammar.


~~~{.ocaml}

type rhs3 = symbol minre

type parse_rule3 = nonterm * symbol list minre

type grammar3 = parse_rule3 list



~~~

## FSM to regexp

~~~{.ocaml}

(* for the proof, we wish to show that any plus expression notcaneps;
   this is true initially; new pluses can be added from self-edges; so
   we need that any self-edge notcaneps; new self-edges arise from
   eliminating a node v, with edges from u to v and v to u; when we
   eliminate such nodes v, we need to ensure that we don't make a
   self-edge that caneps, but we still cover all the possibilities; in
   the definition of min_caneps, we can assume that any plus expressions
   notcaneps; we therefore need to consider the other possibilities;

   if plus is none, and from and to are [], then we don't add a
   self-edge

   otherwise, plus is some, and we do; there is the possibility that we
   have plus as an empty list; so we also need to ensure this is ruled
   out (which is really an invariant on the datatype, not our alg - we
   should use the type of non-empty lists)

   another point about min_caneps: if we have the invariant on plus,
   then the only way it caneps is if all the from and to atom2s caneps
*)
let rec min_caneps re = (match re with
  | ATOM2 xs -> (xs = []) (* assumes non-empty symbol lists cannot eps *)
  | SEQPLUS2(from,plus,_to) -> (match plus with 
      | None -> (min_caneps from && min_caneps _to)
      | Some xs -> (min_caneps from && (forall min_caneps xs) && min_caneps _to)))

(* the following is equivalent to the above, given the invariant on plus expressions *)
let rec min_caneps2 re = (match re with
  | ATOM2 xs -> (xs = []) (* assumes non-empty symbol lists cannot eps *)
  | SEQPLUS2(from,plus,_to) -> (match plus with 
      | None -> (min_caneps2 from && min_caneps2 _to)
      | Some xs -> false)) (* invariant on plus expressions *)

let mingraph0 = {
   vs1=[];
   es1=[];
   src1=(fun x -> x.src5);
   dst1=(fun x -> x.dst5);
}

(* another version, with minre, min_fsm *)
let min_elim g avoids =
  let f1 v g0 = ( (* for each vertex *)
    if mem v avoids then g0 else
      let ses = self_edges g0 v in
      let ines = subtract (edges_to g0 v) ses in
      let outes = subtract (edges_from g0 v) ses in
      let f2 ine g = (* for each in edge, which is not a self-edge *)
        let f3 oute g = (* for each out edge, which is not a self-edge *)
          (* first deal with self-edges *)
          let plus = (match ses with 
            | [] -> None (* invariant: never a SEQPLUS2(..,Some([]),..) *)
            | _ -> Some(List.map (fun se -> se.lbl5) ses))
          in
          (* update g with edge from ine.src4 to oute.dst5 *)
          (* handle no looping case first *)
          let lbl = (SEQPLUS2(ine.lbl5,None,oute.lbl5)) in
          let newe = { src5=ine.src5; dst5=oute.dst5; lbl5=lbl } in
          let g = (match (ine.src5=oute.dst5) && min_caneps2 lbl with 
            | true -> g (* don't add self-edge with caneps lbl *)
            | false -> { g with es1=insert newe g.es1 })
          in
          (* now deal with looping *)
          let lbl = (SEQPLUS2(ine.lbl5,plus,oute.lbl5)) in
          let newe = { src5=ine.src5; dst5=oute.dst5; lbl5=lbl } in
          let g = (match plus with 
            | None -> g (* no need to add any plus re - we've already done it *)
            | Some xs -> { g with es1=insert newe g.es1 })
          in
          g
        in
        itlist f3 outes g
      in
      let g' = itlist f2 ines g0 in
      { g' with vs1=(subtract g'.vs1 [v]); es1=(subtract g'.es1 (ses@ines@outes)) })
  in
  itlist f1 g.vs1 g

let (_:min_fsm -> 'a list -> min_fsm) = min_elim

~~~

## Basic functions

Compute whether a given symbol can parse the empty string. 


~~~{.ocaml}

let caneps p_of_tm g sym = (
  grammar_to_parser p_of_tm g sym (toinput (full "")) <> [])

let alt_caneps p_of_tm g alt = forall (caneps p_of_tm g) alt

let rhs3_caneps = min_caneps (* FIXME remove this defn *)

~~~


Compute symbols of a grammar.


~~~{.ocaml}

let syms_of_grammar1 = syms_of_grammar

let rec syms_of_rhs3 rhs = (match rhs with
  | ATOM2 syms -> syms
  | SEQPLUS2(from,z,_to) -> (
    let x = syms_of_rhs3 from in
    let y = syms_of_rhs3 _to in
    let z = (match z with | None -> [] | Some(xs) -> unions (List.map syms_of_rhs3 xs)) in
    x@z@y))

let syms_of_parse_rule3 (nt,rhs) = insert (NT(nt)) (syms_of_rhs3 rhs)

let rec syms_of_grammar3 g = 
  unions (List.map syms_of_parse_rule3 g)

~~~

Converting a grammar1 to a grammar2.


~~~{.ocaml}
let minre_of_alt1 alt = ATOM2(alt)

(* the following takes a grammar with symbol list list rhs, and gives one with symbol list rhs *)
let single_of_grammar1 g1 = 
  let rules_of_rhs1 (nt,alts) = List.map (fun alt -> (nt,alt)) alts in
  unions (List.map rules_of_rhs1 g1)

let grammar3_of_grammar1 g1 =
  List.map (fun (nt,alt) -> (nt,minre_of_alt1 alt)) (single_of_grammar1 g1)

let (_:grammar1 -> grammar3) = grammar3_of_grammar1

~~~

# Converting a grammar1 to a min_fsm


First we construct the graph that represents the connections between
symbols.

If there is a rule `E -> N1 .. Nn F M1 Mm` and `N1 .. Nn caneps`, then
any initially terminal rhs in `F` gets added to `E` (with `M1 .. Mm`
suffix), so there is an edge from `F` to `E`, labelled `_ M1 .. Mm`

For every self-cycle `E -> E`, if there is an initially terminal rhs `T N1
.. Nn`, we add `(T N1 .. Nn)+` as a rhs.

For every cycle `E -(_1)-> F .. G -(_n)-> E`, and terminal rhs for `E`:
`T N1 .. Nn`, we then add `(T N1 .. Nn)(_1_2.._n)*` to `E`.

We start constructing the graph with the relevant edges. The nodes are
the nonterminals. The edges are suffixes of an alternative (represented
as an alternative).

FIXME an invariant of `graph1_of_grammar` is that the edges are either
empty, or initially terminal (begin e.g. with E+ etc)


~~~{.ocaml}

let ($) f g x = f(g x)

let graph1_of_grammar1 (caneps:symbol -> bool) g = 
  let vs = syms_of_grammar1 g in
  let f1 sym = (match sym with 
    | TM(tm) -> []
    | NT(nt) -> (
      let rules = List.filter (fun (nt',rhs) -> nt' = nt) g in
      let alts1 = (List.concat $ (List.map snd)) rules in
      (* for every alt, we add some edges FIXME we need to add in Plus1 etc and avoid self-edges with empty (but see below!) *)
      let rec f2 alt es = (match alt with 
        | [] -> es
        | sym'::alt' -> (
          let es' = insert { src3=sym'; dst3=sym; lbl3=alt' } es in
          if caneps sym' then f2 alt' es' else es'))
      in
      itlist f2 alts1 []))
  in
  let es = unions (List.map f1 (vs)) in
  (* filter out self-edges with empty labels *)
  let es = List.filter (fun e -> e.src3<>e.dst3 || e.lbl3 <> []) es in
  { vs1=vs; es1=es; src1=(fun x -> x.src3); dst1=(fun x -> x.dst3) }

let (_:(symbol->bool) -> grammar1 -> (symbol,edge1)graph1) = graph1_of_grammar1


let min_fsm_of_grammar1 caneps g =
  let g1 = graph1_of_grammar1 caneps g in
  let min_edge_of_edge1 e = { src5=e.src3; dst5=e.dst3; lbl5=(minre_of_alt1 e.lbl3) } in
  { vs1=g1.vs1; es1=(List.map min_edge_of_edge1 g1.es1); src1=(fun e -> e.src5); dst1=(fun e -> e.dst5) }

let (_:(symbol->bool) -> grammar1 -> min_fsm) = min_fsm_of_grammar1

(* take a grammar1 and produce an equivalent grammar1 via elim; for each
   nonterminal, elim from terminals to the nonterminal, and that gives
   you a list of alternatives (a list of regexp), which can be mapped
   back to a list of alternatives *)

let regexps_of_symbol caneps g sym0 = 
  let syms = syms_of_grammar g in
  let tms = List.filter is_TM syms in
  (* don't deal with eps here *)
  let tms = List.filter (fun x -> x <> eps) tms in
  let fsm = min_fsm_of_grammar1 caneps g in
  (* add another distinguished node and edge *)
  let new_NT = NT("",None1) in
  (* note the SEQ1([]) in the following has to be removed later on *)
  let fsm = { fsm with vs1=(new_NT::fsm.vs1); es1=({ src5=sym0;dst5=new_NT;lbl5=ATOM2[] }::fsm.es1) } in
  let re tmsym = 
    let g = min_elim fsm [tmsym;new_NT] in
    List.map (fun e -> {e with dst5=sym0}) g.es1
  in
  let res = unions (List.map re tms) in
  res

let (_:(symbol -> bool) -> grammar1 -> symbol -> min_edge list) = regexps_of_symbol

~~~


~~~{.ocaml}

(* putting the whole thing together *)
let initially_terminal_grammar_of_grammar caneps g1 =
  let syms = syms_of_grammar g1 in
  let nts = List.filter is_NT syms in
(*  let nts = List.map dest_NT nts in *)
  let f1 nt = 
    (* for each nt *)
    let res = regexps_of_symbol caneps g1 nt in
    (* below, e.src4 is the terminal; from a terminal "1" with lbl .., we make a lbl "1" .. *)
    let f2 e = { e with lbl5=SEQPLUS2(ATOM2[e.src5],None,e.lbl5) } in
    let res = List.map f2 res in
    let res = List.map (fun e -> e.lbl5) res in
    (* let rexys = List.map elim_STAR1s res in 
    (* the following deals with the snd component of elim_STAR1s - the new nts represent a star of a re *)
    let f (nt,re) = (nt,ALT1[ATOM1(eps);SEQ1[re;ATOM1(NT(nt))]]) in
    let res = unions (List.map (fun (re,xys) -> insert (nt,re) (List.map f xys)) rexys) in 
    let rs = grammar1_of_grammar2 res in
    rs *)
    List.map (fun re -> (nt,re)) res
  in
  let r = unions (List.map f1 nts) in
  (* List.map (fun (nt,p) -> (nt,[p])) r *)
  r

let (_:(symbol -> bool) -> grammar1 -> (symbol * symbol list minre)list) = initially_terminal_grammar_of_grammar

(* optimize the minre by combining empty sequences etc; FIXME we may want to define a canonical form for these expressions *)
let rec optimize re = (match re with
  | ATOM2 _ -> re
  | SEQPLUS2(xs,ys,zs) -> (
    match (optimize xs,ys,optimize zs) with 
      | ((ATOM2 []),None,(ATOM2 zs)) -> (ATOM2 zs)
      | ((ATOM2 xs),None,(ATOM2 [])) -> (ATOM2 xs)
      | (xs,None,ys) -> SEQPLUS2(xs,None,ys)
      | (xs,Some ys,zs) -> SEQPLUS2(xs,Some(List.map optimize ys),zs)))

let rec canonicalize re = (match re with
  | ATOM2 [] -> []
  | ATOM2 xs -> [ATOM3 xs]
  | SEQPLUS2(xs,None,zs) -> ((canonicalize xs)@(canonicalize zs))
  | SEQPLUS2(xs,Some ys,zs) -> ((canonicalize xs)@[PLUS3 (List.map canonicalize ys)]@(canonicalize zs)))

let (_:symbol list minre -> symbol list linre list) = canonicalize
  
(* FIXME remaining is to restrict to non-eps terminals, and deal with caneps separately *)  

let eps_rules_of_grammar caneps g =
  let nts = List.filter is_NT (syms_of_grammar g) in
  let f symnt = if caneps symnt then [(dest_NT symnt,[[eps]])] else [] in
  List.concat (List.map f nts)

let (_:(symbol -> bool) -> grammar1 -> parse_rule1 list) = eps_rules_of_grammar

(* now we need a version of the parser that is memoized but doesn't bother with context etc *)


~~~


~~~{.ocaml}
(* final double-semi-colon, for using via ocaml <xyz.ml *)
;;

~~~

