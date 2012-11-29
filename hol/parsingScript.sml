(* * prelude *)

(* Hi-lock: (("^ *\\(have\\|want\\).*" (0 (quote hi-green-b) t))) *)

(*

This is a formalization of the paper:

  Simple, functional, sound and complete parsing for all context-free grammars,
  by Tom Ridge, University of Leicester

  Under submission for publication

*)

val _ = app load ["numLib","finite_mapTheory", "stringTheory", "unwindLib","prim_recTheory"]; (* unwindLib for tactics; prim_rec for measure *)

val _ = Globals.linewidth:=120;

(* FIXME change to HOL_Interactive.toggle_quietdec() *)
fun myquietdec n = PolyML.print_depth n; (* EXPORT poly *)

myquietdec 0;
open pred_setTheory;
open finite_mapTheory;
myquietdec 100;



(* the following is taken from HOL/src/proofman/goalStack.sml, and modified to print goal at bottom *)
(* FIXME in new versions of HOL, this can be replaced by toggling some variables, see http://hol.svn.sourceforge.net/hol/?rev=9037&view=rev *)

val print_fvs = ref false;

fun ppgoal ppstrm (asl,w) =
   let open Portable
       val {add_string, add_break,
            begin_block, end_block, add_newline, ...} = with_ppstream ppstrm
       val pr = Parse.pp_term ppstrm
       fun pr_index (i,tm) =
            (begin_block CONSISTENT 0;
             add_string (Int.toString i^".  ");
             pr tm; end_block())
       fun pr_indexes [] = raise ERR "pr_indexes" ""
         | pr_indexes [x] = pr x
         | pr_indexes L = pr_list pr_index (fn () => ()) add_newline
                                  (rev (Lib.enumerate 0 (rev asl)));
   in
     begin_block CONSISTENT 0;
     (case asl
        of [] => ()
         | _  => ( begin_block CONSISTENT 2;
                   pr_indexes asl;
                   add_newline ();
                   add_string (!Globals.goal_line);
		   end_block ()));
     add_newline ();
     pr w;
     add_newline ();
     if !print_fvs then let
         val fvs = Listsort.sort Term.compare (free_varsl (w::asl))
         fun pr_v v = let
           val (n, ty) = dest_var v
         in
           begin_block INCONSISTENT 2;
           add_string n; add_break(1,0);
           Parse.pp_type ppstrm ty;
           end_block()
         end
       in
         if (not (null fvs)) then
           (if (not (null asl)) then add_newline() else ();
            add_string "Free variables"; add_newline();
            add_string "  ";
            begin_block CONSISTENT 0;
            pr_list pr_v (fn () => ()) (fn () => add_break(5,0)) fvs;
            end_block ();
            add_newline(); add_newline())
         else ()
       end
     else ();
     end_block ()
   end
   handle e => (Lib.say "\nError in attempting to print a goal!\n";  raise e);

set_goal_pp ppgoal;


use "tactic.sml"; open tactic; (* EXPORT tactic.sml *)

(* srw_ss was proving too much; LIST EQ: in general the simplifier should not
solve an equality that it wouldn't also use as a rewrite; REDUCE was changing c
- b <> 0 to ~ (c <= b) *)

val tmp = diminish_srw_ss ["list EQ","REDUCE","ARITH_RWTS"];

(* I find ASCII easier to read than (single width) unicode *)
val _ = set_trace "Unicode" 0;

val _ = new_theory "parsing";

(* * library stuff *)

val failwith_def = Define `
failwith (s:string) = (ARB:'a)
`;

(* * types *)

val pre_substring_def = type_abbrev("pre_substring", ``:string # num # num``);

val slh = ``(s,l,h):pre_substring``;

val wf_substring_def = Define `
wf_substring ^slh = l <= h /\ h <= STRLEN s
`;

g `
? s. wf_substring s
`;
er `("",0,0)`;
e(ssimp[wf_substring_def]);
e(numLib.ARITH_TAC);
val exists_wf_substring = top_thm();

(* declare the type of well formed substrings *)

val ty_substring_def = new_type_definition("substring",exists_wf_substring);

val ty_substring_bijs = define_new_type_bijections{name="ty_substring_bijs", ABS="myabs", REP="myrep", tyax=ty_substring_def};

val [[myabs_myrep,ty_substring_2]] = [CONJUNCTS ty_substring_bijs];

g `
wf_substring r ==> (myrep (myabs r) = r)
`;
e(tac[ty_substring_2]);
val myrep_myabs = top_thm();

val myabs_11 = (prove_abs_fn_one_one ty_substring_bijs);
val myabs_onto = (prove_abs_fn_onto  ty_substring_bijs);
val myrep_11 = (prove_rep_fn_one_one ty_substring_bijs);
val myrep_onto = (prove_rep_fn_onto  ty_substring_bijs);

val ty_substring_simps = [myabs_myrep,myrep_myabs,myabs_11,myrep_11];

(* FIXME remove for final version, replace with string *)
val _ = new_type("ty_term",0);

val term_def = type_abbrev("term",``:ty_term``);

val _ = Parse.disable_tyabbrev_printing "term";

(* FIXME remove for final version, replace with string *)
val _ = new_type("ty_nonterm",0);

val nonterm_def = type_abbrev("nonterm",``:ty_nonterm``);

val _ = Parse.disable_tyabbrev_printing "nonterm";

(*val _ = type_abbrev("singleton",``:substring``);*)

val symbol_def = Hol_datatype `
symbol = TM of term | NT of nonterm
`;

val parse_rule_def = type_abbrev("parse_rule",``:nonterm # ((symbol list) list)``);

val grammar_def = type_abbrev("grammar",``:parse_rule list``);

val parse_tree_def = Hol_datatype `
parse_tree = NODE of nonterm # parse_tree list | LF of term # substring
`;

val local_context_def = type_abbrev("local_context",``:(nonterm # substring) list``);

val ty_input_def = Hol_datatype `
ty_input = <|
  lc1 : local_context;
  sb1 : substring
|>
`;

(* mathematically this is what we are really interested in FIXME should take strings? *)
val simple_parser_def = type_abbrev("simple_parser", ``:substring -> parse_tree list``);

(* parser is an implementation type: it returns parses of prefixes *)
val parser_def = type_abbrev("parser",``:ty_input -> ('a # substring) list``);

(* p_of_tm is an implementation type: it returns parses of prefixes *)
val ty_p_of_tm_def = type_abbrev("ty_p_of_tm", ``:term -> substring parser``);

val ty_ss_of_tm_def = type_abbrev("ty_ss_of_tm", ``:term -> substring set``);

(* * substrings *)

val string_def = Define `
string s = let (s,l,h) = myrep s in s
`;

(* FIXME in the following do we want h < LENGTH s? *)

val low_def = Define `
low s = let (s,l,h) = myrep s in l
`;

val high_def = Define `
high s = let (s,l,h) = myrep s in h
`;

val len_def = Define `
len s = let (s,l,h) = myrep s in h - l
`;

val full_def = Define `
full s = myabs (s,0,STRLEN s)
`;

val content_def = Define `
content s = SUBSTRING(string s, low s, len s)
`;

val inc_low_def = Define `
inc_low n s = let (s,l,h) = myrep s in myabs (s,l+n,h)
`;

val dec_high_def = Define `
dec_high n s = let (s,l,h) = myrep s in myabs (s,l,h-n)
`;

val inc_high_def = Define `
inc_high n s = let (s,l,h) = myrep s in myabs (s,l,h+n)
`;

val concatenate_two_def = Define `
concatenate_two s1 s2 =
  if (* FIXME_ty_substring wf_substring s1 /\ wf_substring s2 /\ *) (string s1 = string s2) /\ (high s1 = low s2) then
    SOME (myabs (string s1,low s1,high s2)) else NONE
`;

val concatenate_list_def = Define `
concatenate_list ss = case ss of [] -> NONE
  || s1::ss1 -> (case ss1 of [] -> (SOME s1) (* FIXME_ty_substring if wf_substring s1 T then SOME s1 else NONE *)
    || _1::_2 -> (case concatenate_list ss1 of NONE -> NONE
      || SOME s2 -> concatenate_two s1 s2))
`;


(* * term, nonterm, parse_rule, grammar, parse_tree, to_input *)

val toinput_def = Define `
toinput s = <| lc1 := []; sb1 := s |>
`;

val is_NT_def = Define `
is_NT sym = case sym of TM _ -> F || NT _ -> T
`;

val dest_NT_def = Define `
dest_NT sym = case sym of NT x -> x || _ -> failwith "dest_NT"
`;

val is_TM_def = Define `
is_TM sym = case sym of TM _ -> T || NT _ -> F
`;

(* may contain duplicates *)
val symbols_of_parse_rule_def = Define `
symbols_of_parse_rule (nt,alts) = (NT nt)::(FLAT alts)
`;

val _ = ``(_:parse_rule->symbol list) = symbols_of_parse_rule``;

val symbols_of_grammar_def = Define `
symbols_of_grammar g = (FLAT o MAP symbols_of_parse_rule) g
`;

val nonterms_of_grammar_def = Define `
nonterms_of_grammar g =
  MAP dest_NT (FILTER is_NT (symbols_of_grammar g))
`;

val parse_tree_size_def = DB.fetch "-" "parse_tree_size_def";

val is_NODE_def = Define `
is_NODE pt = case pt of NODE _ -> T || _ -> F
`;

val dest_NODE_def = Define `
dest_NODE pt = case pt of
  NODE(nt,pts) -> (NT nt,pts)
  || LF(tm,s) -> failwith "dest_NODE"
`;

val children_def = Define `
children pt = (SND o dest_NODE) pt
`;

val root_def = Define `
root pt = case pt of NODE(nt,pts) -> NT nt || LF(tm,s) -> TM tm
`;


(* syntax *)

val mythen_def = new_infixr_definition(
  "mythen",
  --`$**> (p1:'a parser) (p2:'b parser) = \ i.
  let f (e1,s1) =
    MAP (\ (e2,s2). ((e1,e2),s2)) (p2 <| lc1:=i.lc1; sb1:=s1 |>)
  in
  (FLAT o (MAP f) o p1) i`--,
  501);


(* * common functions *)

val substr_def = Define `
substr i = i.sb1
`;

val lift_def = Define `
lift f i = i with <| sb1:=(f i.sb1) |>
`;




(* * combinators *)

val always_def = Define `
always = (\ i. [([],substr i)]):'a list parser
`;

val never_def = Define `
never = (\ i. []):'a parser
`;


val myor_def = new_infixr_definition(
  "myor",
  ``$||| (p1:'a parser) (p2:'a parser) = \ i. APPEND (p1 i) (p2 i)``,
  501);

val myrr_def = new_infixr_definition(
  "myrr",
  ``$>> (p:'a parser) (f:'a -> 'b) = (MAP (\ (e,s). (f e, s))) o p``,
  503);

val ignr_last_def = Define `
ignr_last (p:'a parser) = \ i.
  if len (substr i) = 0 then [] else
  let dec = dec_high 1 in
  let inc (e,s) = (e,inc_high 1 s) in
  ((MAP inc) o p o (lift dec)) i
`;

val then_list_def = Define `
then_list (ps:'a parser list) = case ps of
  [] -> always
  || p::ps -> ((p **> (then_list ps))
    >> (\ (x,xs). x::xs))
`;

val then_list_two_def = Define `
then_list2 nt = \ ps. 
  then_list ps >> (\ xs. NODE(nt,xs))
`;

val or_list_def = Define `
or_list (ps:'a parser list) = case ps of
  [] -> never
  || p::ps -> (p ||| (or_list ps))
`;


(* * proof *)
(*  + proof: arithmetic *)

g `
x <= x /\ (x + 0 = x) /\ x <= x + 1 /\ x < x + 1 /\ (SUC n - 1 = n) /\ ~(x < 0) /\ x < 1 + x /\ (1 + x - 1 = x) /\ (1 + x <> 0)
`;
e(numLib.ARITH_TAC);
val arith_simps = top_thm();

g `
! x y z:num. (x+y = y+x) /\ (x + (y + z) = ((x+y)+z)) /\ (x < y ==> x < y+z) /\ (x <= y /\ y <= x ==> (x = y))
/\ (x <= y /\ y < x ==> F)
/\ (x <= y /\ x <> y ==> x < y)
/\ (x <= y ==> (x = y) \/ x <= y - 1)
/\ (x <= y /\ y <= z ==> x <= z)
/\ ((x = y) ==> x <= y)
`;
e(numLib.ARITH_TAC);
val arith_thms = top_thm();

g `
! x y z w:num.
((x=y) ==> x <= y)
/\ (x <= y /\ y <= x ==> (x = y))
/\ (x <= y /\ y <= z ==> x <= z)
/\ (x <= y ==> x <= y + z)
/\ (x <= y /\ z <= w ==> x + z <= y + w)
`;
e(numLib.ARITH_TAC);
val le_thms = top_thm();


g `
((x < y) = ((x <= y) /\ x <> y))
/\ ((x < y) = (x+1<=y))
/\ (x < y /\ z <= w ==> x + z < y + w)
/\ (x+y = y+x)
/\ (~(x<=y) <=> y < x) 
`;
e(numLib.ARITH_TAC);
val less_le = top_thm();

g `
(x+y = y+x) /\ (x + (y + z) = ((x+y)+z)) /\ (x < y ==> x < y+z) /\ (x < y /\ y < z ==> x < z) (* this seems to speed up metis *)
`;
e(numLib.ARITH_TAC);
val plus_thms = top_thm();


(*  + proof: library stuff *)

g `
(? x. P x) ==> P (CHOICE P)
`;
e(ASSUME_TAC CHOICE_DEF);
xal `P`;
e(intros);
e(ssimp[]);
il 0;
 e(intros);
 e(ssimp[EMPTY_DEF]);
e(ssimp[SPECIFICATION] THEN NO_TAC);
val EXISTS_CHOICE = top_thm();

val EXISTS_CHOICE = Q.store_thm("EXISTS_CHOICE", `
(? x. P x) ==> P (CHOICE P)
`,
ASSUME_TAC CHOICE_DEF THEN
FORALLL_X_TAC `P` THEN
intros THEN
ssimp[] THEN
ITAC_OF_THM_TAC IMPL_TAC 0 THENL [
 intros THEN
 ssimp[EMPTY_DEF],
ssimp[SPECIFICATION] THEN NO_TAC]
);


g `
(! nt. MEM nt nts ==> f nt <= f' nt) ==> SUM (MAP f nts) <= SUM (MAP f' nts)
`;
e(Induct_on `nts`);
e(ssimp[arith_simps] THEN NO_TAC);
e(ssimp[]);
e(intros);
e(ssimp[]);
xal `h`;
e(ssimp[]);
e(tac[le_thms]);
val SUM_MAP_LEQ = top_thm();

g `
(! nt. MEM nt nts ==> f nt <= f' nt) /\ (? nt. MEM nt nts /\ f nt < f' nt) ==> SUM (MAP f nts) < SUM (MAP f' nts)
`;
e(Induct_on `nts`); e(ssimp[] THEN NO_TAC);
e(intros);
e(ssimp[]);
dl();
 e(ssimp[]);
 e(tac[le_thms,less_le,SUM_MAP_LEQ]);

 e(ssimp[]);
 il 2; e(tac[]);
 xal `h`;
 e(ssimp[]);
 e(tac[less_le]);
val SUM_MAP_LESS = top_thm();


(*  + proof: parse tree size *)

g `
! pt. MEM pt pts ==> parse_tree_size pt < parse_tree_size (NODE(nt,pts))
`;
e(Induct_on `pts`);
 e(ssimp[] THEN NO_TAC);

 e(intros);
 xal `pt`;
 e(ssimp[]);
 dl();
  e(ssimp[parse_tree_size_def]);
  e(numLib.ARITH_TAC);

  e(ssimp[parse_tree_size_def]);
  have `(? x. parse_tree_size pt = x) /\ (? y. parse_tree2_size pts = y) /\ (? z. parse_tree_size h = z)`; e(tac[]);
  e(elims);
  e(ssimp[]);
  e(Q.PAT_UNDISCH_TAC `x < 1 + (1 + y)`);
  e(numLib.ARITH_TAC);
val MEM_pt_pts_parse_tree_size = top_thm();

(*  + proof: substrings and input cases *)


g `
? x1 x2 x3. x = (x1,x2,x3)
`;
e(Cases_on `x`);
e(Cases_on `r`);
e(tac[]);
val tcases = top_thm();

g `
? a b c. (s = myabs (a,b,c)) /\ wf_substring (a,b,c)
`;
e(tac[myabs_myrep,ty_substring_2,tcases]);
val tcases_2 = top_thm();


g `
wf_substring (a,b,c) /\ c-b <> 0 ==> wf_substring (a,b,c-1)
`;
e(intros);
e(ssimp[wf_substring_def,inc_high_def,low_def,high_def,dec_high_def,string_def,len_def,arithmeticTheory.NOT_LESS_EQUAL,concatenate_two_def]);
have `! x. (c - b <> 0 /\ b <= c ==> b <= c - 1) /\ (c <= x ==> c -1 <= x)`; e(numLib.ARITH_TAC);
e(tac[]);
val wf_substring_dec_high = top_thm();

g `
len s <> 0 ==> (inc_high 1 (dec_high 1 s) = s)
`;
ir();
e(MY_ASSUME_TAC(tcases_2));
e(elims);
e(ssimp[len_def,inc_high_def,dec_high_def,LET_THM]);
e(ssimp ty_substring_simps);
have `wf_substring (a,b,c-1)`; e(tac[wf_substring_dec_high]);
e(ssimp ty_substring_simps);
have `c - b <> 0 ==> (c - 1 + 1 = c)`; e(numLib.ARITH_TAC);
e(ssimp[] THEN NO_TAC);
val inc_high_one_dec_high_one = top_thm();

g `
len s <> 0 ==> len (dec_high 1 s) < len s
`;
e(intros);
e(MY_ASSUME_TAC(tcases_2));
e(elims);
e(ssimp[len_def,dec_high_def,LET_THM]);
e(ssimp ty_substring_simps);
have `wf_substring (a,b,c-1)`; e(tac[wf_substring_dec_high]);
e(ssimp ty_substring_simps);
have `(c - b <> 0) ==> (c - 1 - b < c - b)`; e(numLib.ARITH_TAC);
e(tac[]);
val len_dec_high = top_thm();

g `
(wf_substring (a,b,c) /\ wf_substring (a,c,c') ==> wf_substring (a,b,c'))
/\ (wf_substring (a,b,c) ==> wf_substring (a,b,b) /\ wf_substring (a,c,c))
/\ (wf_substring (a,b,c) /\ c - b <> 0 ==> wf_substring (a,b,c-1))
/\ (wf_substring (a,b',c) /\ wf_substring (a,b,c-1) ==> wf_substring (a,b,c))
/\ wf_substring (a,0,0)
`;
e(intros);
e(ssimp[wf_substring_def]);
e(ssimp[arith_simps]);
have `? x. STRLEN a = x`; e(tac[]);
e(elims);
e(ssimp[]);
e(REMOVE_VAR_TAC `a`);
e(REPEAT (Q.PAT_UNDISCH_TAC `_`));
e(numLib.ARITH_TAC);
val wf_substring_thms = top_thm();

g `
(concatenate_two s1 s2 = SOME s3)
==> (* FIXME_ty_substring wf_substring s1 /\ wf_substring s2 /\ wf_substring s3 /\ *) (low s3 = low s1) /\ (high s3 = high s2) /\ (high s1 = low s2) /\ (high s1 <= high s3) /\ (low s3 <= low s2) /\ (string s1 = string s2) /\ (string s2 = string s3) /\ ((s2 = s3) \/ len s2 < len s3)
`;
e(intros);
e(ssimp[concatenate_two_def]);
e(MY_ASSUME_TAC(INST [``s:substring``|->``s1:substring``] tcases_2));
e(elims);
e(MY_ASSUME_TAC(INST [``s:substring``|->``s2:substring``] tcases_2));
e(elims);
e(MY_ASSUME_TAC(INST [``s:substring``|->``s3:substring``] tcases_2));
e(elims);
e(ssimp[low_def,high_def,string_def,len_def,LET_THM]);
e(ssimp ty_substring_simps);
have `wf_substring (a',b,c')`; e(tac[wf_substring_thms]);
e(ssimp ty_substring_simps);
e(ssimp[wf_substring_def]);
have `? x. STRLEN a'' = x`; e(tac[]);
e(elims);
e(ssimp[]);
e(REMOVE_VARS_TAC [`s1`,`s2`,`s3`,`a`,`a'`,`a''`]);
e(Q_THIN_TAC `T`);
e(REPEAT (Q.PAT_UNDISCH_TAC `_`));
e(numLib.ARITH_TAC);
val concatenate_two_SOME = top_thm();

(*
g `
(concatenate_list xs = SOME x) ==> wf_substring x
`;
e(Cases_on `xs`);
 e(ssimp[concatenate_list_def_2] THEN NO_TAC);

 e(ssimp[concatenate_list_def_2]);
 e(Cases_on `t`);
  e(ssimp[]);
  e(tac[]);

  e(ssimp[]);
  e(Cases_on `concatenate_list (h'::t')`);
   e(ssimp[] THEN NO_TAC);

   e(ssimp[]);
   e(tac[concatenate_two_SOME]);
val concatenate_list_SOME = top_thm();
*)

g `
(* wf_substring s ==> (? s'. wf_substring s' /\ (concatenate_two s' s = SOME s)) /\ (? s'. wf_substring s' /\ (concatenate_two s s' = SOME s)) *)
(? s'. concatenate_two s' s = SOME s) /\ (? s'. concatenate_two s s' = SOME s)
`;
e(MY_ASSUME_TAC(tcases_2));
e(elims);
cr();
 have `wf_substring (a,b,b)`; e(tac[wf_substring_thms]);
 er `myabs (a,b,b)`;
 e(ssimp[concatenate_two_def]);
 e(ssimp ty_substring_simps);
 e(ssimp[string_def,low_def,high_def,LET_THM]);
 e(ssimp ty_substring_simps THEN NO_TAC);

 have `wf_substring (a,c,c)`; e(tac[wf_substring_thms]);
 er `myabs (a,c,c)`;
 e(ssimp[concatenate_two_def]);
 e(ssimp ty_substring_simps);
 e(ssimp[string_def,low_def,high_def,LET_THM]);
 e(ssimp ty_substring_simps THEN NO_TAC);
val exists_concatenate_two_equals = top_thm();
  

g `
? lc sb. i = <| lc1:=lc; sb1:=sb |>
`;
e(tac[DB.fetch "parsing" "ty_input_literal_nchotomy"]);
val icases_thm = top_thm();

(*  + proof: combinators *)

val or_list_def_2 = rewrite_def or_list_def ``ps:'a parser list``;

val then_list_def_2 = rewrite_def then_list_def ``ps:'a parser list``;

g `
! v s' i.
(? p. MEM p ps
/\ MEM (v,s') (p i))
<=> MEM (v,s') (or_list ps i)
`;
e(Induct_on `ps`);
 e(ssimp[or_list_def,never_def]);

 e(ssimp[]);
 e(intros);
 e(elims);
 e(EQR_TAC);
  (* ==> *)
  e(elims);
  dl();
   e(ssimp[or_list_def_2]);
   e(ssimp[myor_def] THEN NO_TAC);

   e(ssimp[or_list_def_2]);
   e(ssimp[myor_def]);
   e(tac[]);

  (* <== *)
  e(ssimp[or_list_def_2]);
  e(ssimp[myor_def]);
  dl();
   e(tac[]);

   e(tac[]);
val or_list_thm = top_thm();

g `
MEM p ps
/\ MEM (v,s') (p i)
==> MEM (v,s') (or_list ps i)
`;
e(tac[or_list_thm]);
val or_list_1 = top_thm();

g `
MEM (v,s') (or_list ps i)
==>
(? p. MEM p ps /\ MEM (v,s') (p i))
`;
e(tac[or_list_thm]);
val or_list_2 = top_thm();

g `
MEM (NODE(nt,pts),s_rem) (then_list2 nt2 ps i) ==> (nt2 = nt)
`;
e(ssimp[then_list_two_def]);
e(ssimp[myrr_def]);
e(ssimp[listTheory.MEM_MAP]);
e(intros);
e(elims);
e(Cases_on `y` THEN ssimp[] THEN NO_TAC);
val then_list_2_thm = top_thm();

g `
(concatenate_list (MAP THE (MAP (substring_of':parse_tree->substring option) pts)) = SOME s_pts)
==> MEM (pt,THE(concatenate_two s_pts s_rem)) (x <|lc1 := lc; sb1 := s_tot|>)
==> MEM (pts,s_rem) ((then_list xs) <|lc1 := lc; sb1 := THE(concatenate_two s_pts s_rem)|>)
==> MEM (pt::pts,s_rem) ((then_list (x::xs)) <|lc1 := lc; sb1 := s_tot|>)
`;
e(intros);
e(ssimp[then_list_def_2]);
e(ssimp[mythen_def]);
e(ssimp[LET_THM]);
e(ssimp[myrr_def]);
e(ssimp[listTheory.MEM_MAP]);
er `((pt,pts),s_rem)`;
e(ssimp[]);
e(ssimp[listTheory.MEM_FLAT]);
er `MAP (\ (e2,s2). ((pt,e2),s2)) (then_list xs <|lc1 := lc; sb1 := THE(concatenate_two s_pts s_rem)|>)`;
e(ssimp[]);
e(ssimp[listTheory.MEM_MAP]);
cr();
 er `(pt,THE (concatenate_two s_pts s_rem))`;
 e(ssimp[] THEN NO_TAC);

 e(ssimp[]);
 er `(pts,s_rem)`;
 e(ssimp[] THEN NO_TAC);
val MEM_CONS_then_list = top_thm();


g `
(! x. MEM x xs ==> (f x i = f' x i))
==> (or_list (MAP f xs) i = or_list (MAP f' xs) i)
`;
e(Induct_on `xs`);
 e(ssimp[or_list_def_2] THEN NO_TAC);

 e(ssimp[or_list_def_2]);
 e(intros);
 il 0; e(tac[]);
 xal `h`;
 e(ssimp[]);
 e(ssimp[myor_def]);
val or_list_cong = top_thm();


g `
MEM ([],r) (then_list ps i) ==> (ps = [])
`;
e(Cases_on `ps`);
 e(ssimp[]);
 
 e(ssimp[then_list_def_2]);
 e(ssimp[myrr_def]);
 e(ssimp[listTheory.MEM_MAP]);
 e(intros);
 e(Cases_on `y` THEN ssimp[]);
 e(Cases_on `q` THEN ssimp[]);
val MEM_nil_then_list = top_thm();
 

g `
MEM (pt::pts,s_rem) (then_list (p::ps) <| lc1:=lc; sb1:=sb |>) ==> ? s_rem'. MEM (pt,s_rem') (p <| lc1:=lc; sb1:=sb |>) /\ MEM (pts,s_rem) (then_list ps <| lc1:=lc; sb1:=s_rem' |>)
`;
e(intros);
e(ssimp[then_list_def_2]);
e(ssimp[mythen_def,LET_THM,myrr_def]);
e(ssimp[listTheory.MEM_MAP]);
e(Cases_on `y` THEN ssimp[]);
e(Cases_on `q` THEN ssimp[]);
e(ssimp[listTheory.MEM_FLAT]);
e(ssimp[listTheory.MEM_MAP]);
e(Cases_on `y` THEN ssimp[]);
e(ssimp[listTheory.MEM_MAP]);
e(Cases_on `y` THEN ssimp[]);
e(tac[]);
val MEM_cons_then_list = top_thm();


g `
! pts s_rem lc s_tot. MEM (pts,s_rem) (then_list ps <| lc1:=lc; sb1:=s_tot |>) ==> (LENGTH pts = LENGTH ps)
`;
e(Induct_on `ps`);
 e(ssimp[then_list_def_2,always_def] THEN NO_TAC);

 e(intros);
 e(RENAME_TAC [``h:'a parser``|->``p:'a parser``]);
 e(Cases_on `pts`);
  have `p::ps = []`; e(tac[MEM_nil_then_list]);
  e(ssimp[] THEN NO_TAC);
 e(RENAME_TAC [``h:'a``|->``pt:'a``,``t:'a list``|->``pts:'a list``]);
 have `? s_rem'. MEM (pt,s_rem') (p <| lc1:=lc; sb1:=s_tot |>) /\ MEM (pts,s_rem) (then_list ps <| lc1:=lc; sb1:=s_rem' |>)`; 
  e(tac[MEM_cons_then_list]);
 e(elims);
 e(ssimp[]);
 e(tac[]);
val LENGTH_pts_LENGTH_ps = top_thm();

(* * update_lctxt, check_and_upd_lctxt *)

val update_lctxt_def = Define `
update_lctxt nt (p:'a parser) = \ i.
  p (i with <| lc1:=(nt,i.sb1)::i.lc1 |>)
`;

val EQUAL = Type.compare (``:nonterm -> 'a parser -> 'a parser``, type_of ``update_lctxt``);

val check_and_upd_lctxt_def = Define `
check_and_upd_lctxt nt (p:'a parser) = \ i.
  let should_trim = 
    EXISTS ((=) (nt,i.sb1)) i.lc1 in
  if should_trim /\ (len i.sb1 = 0) then
    []
  else if should_trim then
    (ignr_last (update_lctxt nt p)) i
  else
    (update_lctxt nt p) i
`;


(* * definitions for proof (must be here if we want to convince Hol that grammar_to_parser exists *)

val wf_grammar_def = Define `
wf_grammar (g:grammar) = ! rhs. 
  MEM rhs (MAP SND g) /\ MEM [] rhs ==> F
`;

val measure_def = Define `
measure g i =
  let nts = nonterms_of_grammar g in
  let f nt = len i.sb1 + (if MEM (nt,i.sb1) i.lc1 then 0 else 1) in
  SUM(MAP f nts)
`;

(*  let lc = FILTER (\ (nt,s). s = i.sb1) i.lc1 in (* FIXME need wellformedness of contexts? *) *)


(* return all subtrees; assumes substring_of pt <> NONE *)
val _ = Hol_defn "subtrees" `
subtrees pt = case pt of
  NODE(nt,pts) -> pt::((FLAT o (MAP subtrees)) pts)
  || LF(tm,s) -> [pt]
`;

(* this defn produces a resonable termination condition *)
val pre_subtrees_def = Hol_defn "subtrees" `
subtrees pt = case pt of
  NODE(nt,pts) -> pt::((FLAT (MAP subtrees pts)))
  || LF(tm,s) -> [pt]
`;

val _ = Defn.tgoal pre_subtrees_def;
p();
er `prim_rec$measure parse_tree_size`;
cr();
 e(tac[prim_recTheory.WF_measure]);

 e(intros);
 e(ssimp[prim_recTheory.measure_thm]);
 e(tac[MEM_pt_pts_parse_tree_size]);
val subtrees_def = CONJUNCT1 (top_thm());

val proper_subtrees_def = Define `
proper_subtrees pt = TL (subtrees pt)
`;

val pre_wf_prs_tree_def = Hol_defn "wf_prs_tree" `
wf_prs_tree pt = case pt of
  NODE(nt,pts) -> (pts <> [] /\ EVERY wf_prs_tree pts)
  || LF(tm,s) -> T (* FIXME_ty_substring wf_substring s *)
`;

val _ = Defn.tgoal pre_wf_prs_tree_def;
p();
er `prim_rec$measure parse_tree_size`;
cr();
 e(tac[prim_recTheory.WF_measure]);

 e(intros);
 e(ssimp[prim_recTheory.measure_thm]);
 e(tac[MEM_pt_pts_parse_tree_size]);
val wf_prs_tree_def = CONJUNCT1 (top_thm());


val pre_substring_of_def = Hol_defn "substring_of" `
substring_of pt = case pt of
  NODE(nt,pts) -> (
      let ss = MAP substring_of pts in
      if EVERY IS_SOME ss then concatenate_list (MAP THE ss) else NONE)
  || LF(tm,s) -> SOME s (* FIXME_ty_substring (if wf_substring s then SOME s else NONE) *)
`;

val _ = Defn.tgoal pre_substring_of_def;
p();
er `prim_rec$measure parse_tree_size`;
cr();
 e(tac[prim_recTheory.WF_measure]);

 e(intros);
 e(ssimp[prim_recTheory.measure_thm]);
 e(tac[MEM_pt_pts_parse_tree_size]);
val substring_of_def = CONJUNCT1 (top_thm());

(* FIXME combine the following with wf_prs_tree *)

val wf_parse_tree_def = Define `
wf_parse_tree pt =
  wf_prs_tree pt
  /\ substring_of pt <> NONE
`;

val matches_pt_def = Define `
matches_pt pt pt' =
  (root pt' = root pt)
  /\ (substring_of pt' = substring_of pt)
`;

val bad_root_def = Define `
bad_root pt = EXISTS (matches_pt pt) (proper_subtrees pt)
`;

val good_tree_def = Define `
good_tree pt = EVERY (\ pt. ~(bad_root pt)) (subtrees pt)
`;

(* to prove good_tree_exists_thm, it is simplest to provide a function that builds the good tree *)

val pre_mk_good_tree_def = Hol_defn "mk_good_tree" `
mk_good_tree pt = case pt of
  NODE(nt,pts) -> (
    let pts' = MAP mk_good_tree pts in
    let pt' = NODE(nt,pts') in
    if ~(bad_root pt') then pt' else  (* otherwise pick some good descendant *)
    CHOICE (\ x. MEM x (proper_subtrees pt') /\ matches_pt pt' x))
  || LF(tm,s) -> LF(tm,s)
`;

val _ = Defn.tgoal pre_mk_good_tree_def;
p();
er `prim_rec$measure parse_tree_size`;
cr();
 e(tac[prim_recTheory.WF_measure]);

 e(intros);
 e(ssimp[prim_recTheory.measure_thm]);
 e(tac[MEM_pt_pts_parse_tree_size]);
val mk_good_tree_def = CONJUNCT1 (top_thm());

val pts_of_def = Define `
pts_of ss_of_tm g pt =
  (wf_parse_tree pt)
  /\ (! pt'.
  MEM pt' (subtrees pt)
  ==> case pt' of
    NODE(nt,pts) ->
      EXISTS (\ (nt',alts). (nt' = nt) /\ MEM (MAP root pts) alts) g
    || LF(tm,s) -> s IN (ss_of_tm tm)) (* FIXME? maybe we should not say anything about terminal parsers *)
`;

val _ = ``(_:(term -> substring set) -> grammar -> parse_tree set) = pts_of``;

(* FIXME do we really care about the properties of p_of_tm? *)

val wf_p_of_tm_def = Define `
wf_p_of_tm p_of_tm = ! tm:term.
  let p = p_of_tm tm in
  (! s_pt. ! lc. ! s_rem. ! s_tot.
    MEM (s_pt,s_rem) (p <| lc1 := lc; sb1 := s_tot |>) ==> (concatenate_two s_pt s_rem = SOME s_tot))
  /\ (! s_pt. ! lc. ! lc'. ! s_rem. ! s_rem'. ! s_tot. ! s_tot'.
    (concatenate_two s_pt s_rem = SOME s_tot) /\ (concatenate_two s_pt s_rem' = SOME s_tot')
    ==> ((MEM (s_pt,s_rem) (p <| lc1 := lc; sb1 := s_tot |>)) <=> (MEM (s_pt,s_rem') (p <| lc1 := lc'; sb1 := s_tot' |>))))
`;

val EQUAL = Type.compare (``:ty_p_of_tm -> bool``, type_of ``wf_p_of_tm``);

(* p_of_tm parses prefixes and returns substrings; we want to get all substrings that it may return *)
val ss_of_tm_of_def = Define `
ss_of_tm_of (p_of_tm:ty_p_of_tm) = \ tm:term.
  let p = p_of_tm tm in
  { s | ? i. ? s'. MEM (s,s') (p i) }
`;

val _ = ``ss_of_tm_of:ty_p_of_tm -> term -> substring set``;

(* FIXME in implementations, may prefer to use s' = "" *)
val simple_parser_of_def = Define `
simple_parser_of (p:parse_tree parser) =
  \ s. (MAP FST o FILTER (\ (pt,s'). substring_of pt = SOME s)) (p (toinput s))
`;


(* assumes wf_parse_tree *)
val pre_admits_def = Hol_defn "admits" `
admits lc pt =
  let s_pt = THE(substring_of pt) in
  case pt of
    NODE(nt,pts) -> (~(MEM (nt,s_pt) lc) /\ EVERY (admits ((nt,s_pt)::lc)) pts)
    || LF(_1,_2) -> T
`;

val _ = Defn.tgoal pre_admits_def;
p();
er `prim_rec$measure (parse_tree_size o SND)`;
cr();
 e(tac[prim_recTheory.WF_measure]);

 e(intros);
 e(ssimp[prim_recTheory.measure_thm]);
 e(tac[MEM_pt_pts_parse_tree_size]);
val admits_def = CONJUNCT1 (top_thm());


val sound_def = Define `
sound ss_of_tm g sym q_sym = ! s. ! pt.
  wf_grammar g
  /\ MEM pt (q_sym s)
  ==>
  pt IN (pts_of ss_of_tm g)
  /\ (root pt = sym)
  /\ (substring_of pt = SOME s)
`;

val EQUAL = Type.compare (``:(term -> substring set) -> grammar -> symbol -> simple_parser -> bool``, type_of ``sound``);

val prefix_sound_def = Define `
prefix_sound ss_of_tm g sym p_sym = ! s_tot. ! pt. ! s_rem. ? s_pt. 
  wf_grammar g (* FIXME_ty_substring /\ wf_substring s_tot *)
  /\ MEM (pt,s_rem) (p_sym (toinput s_tot))
  ==>
  pt IN (pts_of ss_of_tm g)
  /\ (root pt = sym)
  /\ (substring_of pt = SOME s_pt)
  /\ (concatenate_two s_pt s_rem = SOME s_tot)
`;

val EQUAL = Type.compare (type_of ``prefix_sound``, ``:(term -> substring set) -> grammar -> symbol -> parse_tree parser -> bool``);

(* typically an infinite number of parse trees, which can't be returned as a list *)
val unsatisfactory_complete_def = Define `
unsatisfactory_complete ss_of_tm g sym q_sym = ! s. ! pt.
  pt IN (pts_of ss_of_tm g)
  /\ (root pt = sym)
  /\ (substring_of pt = SOME s)
  ==>
  MEM pt (q_sym s)
`;

val EQUAL = Type.compare (type_of ``unsatisfactory_complete``,``:(term -> substring set) -> grammar -> symbol -> simple_parser -> bool``);

val complete_def = Define `
complete ss_of_tm g sym q_sym = ! s. ! pt. ? pt'.
  pt IN (pts_of ss_of_tm g)
  /\ (root pt = sym)
  /\ (substring_of pt = SOME s)
  ==>
  matches_pt pt pt' /\ MEM pt' (q_sym s)
`;

val EQUAL = Type.compare (type_of ``complete``, ``:(term -> substring set) -> grammar -> symbol -> simple_parser -> bool``);

val prefix_complete_def = Define `
prefix_complete ss_of_tm g sym p_sym = ! s_tot. ! s_pt. ! s_rem. ! pt. ? pt'.
  (concatenate_two s_pt s_rem = SOME s_tot)
  /\ pt IN (pts_of ss_of_tm g)
  /\ (root pt = sym)
  /\ (substring_of pt = SOME s_pt)
  ==>
  matches_pt pt pt' /\ MEM (pt',s_rem) (p_sym (toinput s_tot))
`;

val EQUAL = Type.compare (type_of ``prefix_complete``, ``:(term -> substring set) -> grammar -> symbol -> parse_tree parser -> bool``);


(* * proof: fiddling with defns *)

val subtrees_def_2 = rewrite_def subtrees_def ``pt:parse_tree``;

val mk_good_tree_def_2 = rewrite_def mk_good_tree_def ``pt:parse_tree``;

val matches_pt_def_2 =  rewrite_def matches_pt_def ``pt:parse_tree``;

val wf_prs_tree_def_2 =  rewrite_def wf_prs_tree_def ``pt:parse_tree``;

val wf_parse_tree_def_2 =  rewrite_def wf_parse_tree_def ``pt:parse_tree``;

val good_tree_def_2 = rewrite_def good_tree_def ``pt:parse_tree``;

val substring_of_def_2 = rewrite_def substring_of_def ``pt:parse_tree``;

val then_list_def_2 = rewrite_def then_list_def ``ps:'a parser list``;

val admits_def_2 = rewrite_def admits_def ``pt:parse_tree``;

val admits_def_3 = rewrite_def admits_def ``lc:local_context``;

val concatenate_list_def_2 = rewrite_def concatenate_list_def ``ss:substring list``;

val root_def_2 = rewrite_def root_def ``pt:parse_tree``;

val or_list_def_2 = rewrite_def or_list_def ``ps:'a parser list``;

val is_NODE_def_2 = rewrite_def is_NODE_def ``pt:parse_tree``;

val dest_NT_def_2 = rewrite_def dest_NT_def ``sym:symbol``;


(* * proof: grammar_to_parser_exists *)
(*  + proof: grammar_to_parser termination *)
(*   . proof: suffix_sound *)

val suffix_sound_def = Define `
suffix_sound p = ! lc s_tot pt s_rem.
  (MEM (pt:'a,s_rem) (p <| lc1 := lc; sb1 := s_tot |>) ==>  (? s_pt. concatenate_two s_pt s_rem = SOME s_tot))
`;

val EQUAL = Type.compare (type_of ``suffix_sound``, ``:('a parser) -> bool``);

g `
(? s_1. concatenate_two s_1 s_b = SOME s_c) /\ (? s_2. concatenate_two s_2 s_e = SOME s_b) ==> (? s_1. concatenate_two s_1 s_e = SOME s_c)
`; 
e(intros);
e(elims);
er `myabs (string s_c, low s_1, high s_2)`;
e(MY_ASSUME_TAC(INST [``s:substring``|->``s_1:substring``] tcases_2));
e(elims);
e(MY_ASSUME_TAC(INST [``s:substring``|->``s_b:substring``] tcases_2));
e(elims);
e(MY_ASSUME_TAC(INST [``s:substring``|->``s_c:substring``] tcases_2));
e(elims);
e(MY_ASSUME_TAC(INST [``s:substring``|->``s_2:substring``] tcases_2));
e(elims);
e(MY_ASSUME_TAC(INST [``s:substring``|->``s_e:substring``] tcases_2));
e(elims);
e(ssimp[concatenate_two_def]);
e(ssimp[inc_high_def,low_def,high_def,dec_high_def,string_def,len_def,arithmeticTheory.NOT_LESS_EQUAL,concatenate_two_def,LET_THM]);
e(ssimp ty_substring_simps);
have `wf_substring (a'''',b''',c'''') /\ wf_substring (a',b,c')`; e(tac[wf_substring_thms]);
e(ssimp ty_substring_simps);
have `wf_substring (a'',b'',b'''')`; e(tac[wf_substring_thms]);
e(ssimp ty_substring_simps);
val suffix_suffix_is_suffix = top_thm();


(*   . proof: then_list_cong *)

(* the following is only needed for showing that the grammar_to_parser function actually exists *)

(* FIXME following is a bit unnatural *)
g `
(! x. MEM x XS ==> suffix_sound (f x))
/\ (! (x:symbol) s_pt s_rem. (concatenate_two s_pt s_rem = SOME s_tot) /\ MEM x XS
  ==> (f x <| lc1 := lc; sb1 := s_rem |> = f' x <| lc1 := lc; sb1 := s_rem |>))
==> (! x. MEM x xs ==> MEM x XS) ==> ! s_pt s_rem. (concatenate_two s_pt s_rem = SOME s_tot) ==> (then_list (MAP (f:symbol->'a parser) xs) <| lc1:=lc; sb1:=s_rem |> = then_list (MAP f' xs) <| lc1:=lc; sb1:=s_rem |>)
`;
ir();
e(elims);
e(Induct_on `xs`);
 e(intros);
 e(ssimp[then_list_def_2] THEN NO_TAC);

 e(intros);
 e(elims);
 e(RENAME_TAC [``h:symbol``|->``sym:symbol``]);
 e(ssimp[then_list_def_2,mythen_def,LET_THM,myrr_def]);
 e(ssimp[]);
 have `(f sym <|lc1 := lc; sb1 := s_rem|>) = (f' sym <|lc1 := lc; sb1 := s_rem|>)`;
  xal `sym`;
  xal `s_pt`;
  xal `s_rem`;
  il 0; e(ssimp[] THEN NO_TAC);
  e(INIT_TAC); 
 e(ssimp[]);
 want `
  (MAP (\ (e1,s1). MAP (\ (e2,s2). ((e1,e2),s2)) (then_list (MAP f xs) <|lc1 := lc; sb1 := s1|>))
        (f' sym <|lc1 := lc; sb1 := s_rem|>))
 =
     (MAP (\ (e1,s1). MAP (\(e2,s2). ((e1,e2),s2)) (then_list (MAP f' xs) <|lc1 := lc; sb1 := s1|>))
        (f' sym <|lc1 := lc; sb1 := s_rem|>))
 `;
  e(tac[]);
 e(MATCH_MP_TAC' listTheory.MAP_CONG);
 cr(); e(tac[]);
 e(intros);
 e(Cases_on `x` THEN ssimp[]);
 e(MATCH_MP_TAC' listTheory.MAP_CONG);
 cr();
  have `suffix_sound (f sym)`; e(tac[]);
  e(Q_THIN_TAC `! x. MEM x XS ==> _`);
  e(ssimp[suffix_sound_def]);
  e(tac[concatenate_two_SOME,suffix_suffix_is_suffix]);

  e(intros);
  e(Cases_on `x` THEN ssimp[] THEN NO_TAC);
val pre_then_list_cong = top_thm();


g `
(! x. MEM x xs ==> suffix_sound (f x))
/\ (! x. MEM x xs ==> suffix_sound (f' x))
/\ (! (x:symbol) s_pt s_rem. (concatenate_two s_pt s_rem = SOME s_tot) /\ MEM x xs 
  ==> (f x <| lc1 := lc; sb1 := s_rem |> = f' x <| lc1 := lc; sb1 := s_rem |>))
==> (then_list (MAP (f:symbol->'a parser) xs) <| lc1:=lc; sb1:=s_tot |> = then_list (MAP f' xs) <| lc1:=lc; sb1:=s_tot |>)
`;
e(intros);
e(elims);
e(MY_ASSUME_TAC (INST [``XS:symbol list``|->``xs:symbol list``,``s_rem:substring``|->``s_tot:substring``] pre_then_list_cong));
il 0; e(tac[]);
il 0; e(tac[]);
e(MY_ASSUME_TAC (INST [``s:substring``|->``s_tot:substring``] exists_concatenate_two_equals));
e(tac[]);
val then_list_cong = top_thm();


(*   . proof: basic measure lemmas *)

g `
len s'' < len s' ==> measure g <| lc1 := lc''; sb1 := s'' |> <= measure g <| lc1 := lc'; sb1 := s' |>
`;
e(intros);
have `? nts. nonterms_of_grammar g = nts`; e(tac[]);
e(elims);
e(ssimp[measure_def,LET_THM]);
e(MATCH_MP_TAC' SUM_MAP_LEQ);
e(intros);
e(ssimp[]);
e(Cases_on `MEM (nt,s'') lc''` THEN ssimp[arith_simps]);
 e(Cases_on `MEM (nt,s') lc'` THEN ssimp[arith_simps]);
  e(tac[less_le]);
  
  e(tac[plus_thms,less_le]);

 e(ssimp[]);
 e(Cases_on `MEM (nt,s') lc'` THEN ssimp[arith_simps]);
  e(tac[less_le]);

  e(tac[less_le]);
val measure_substring = top_thm();



(*   . proof: the comprehensible lemmas *)

(* Hol can't figure out the definition at all; here we give it a bit of help *)

(* rhs of defn; grammar_to_parser has been eta-expanded *)
(* val (_,tm) = dest_eq (snd (dest_thm grammar_to_parser_def)); *)

(* NB the following works even if i is not well-nested *)



g `
((\ i. [(i, s0)]) = p)
==> MEM nt (nonterms_of_grammar g)
==>  ! i' s. MEM (i',s) (check_and_upd_lctxt nt p i) ==> measure g i' < measure g i 
`;
e(intros);
e(SYM_TAC `_ = p`);
e(ssimp[]);
e(Q_THIN_TAC `p = _`);
e(ssimp[check_and_upd_lctxt_def]);
e(Cases_on `EXISTS ($= (nt,i.sb1)) i.lc1`);
 e(ssimp[LET_THM]);
 e(Cases_on `len i.sb1 = 0`); e(ssimp[] THEN NO_TAC); 
 e(ssimp[]);
 e(ssimp[ignr_last_def]);
 e(ssimp[substr_def,LET_THM]);
 e(ssimp[listTheory.MEM_MAP]);
 e(Cases_on `y` THEN ssimp[]);
 e(ssimp[update_lctxt_def]);
 e(REMOVE_VARS_TAC [`q`,`r`,`s`,`i'`]);
 e(ssimp[lift_def]);
 have `? i'. <|lc1 := (nt,dec_high 1 i.sb1)::i.lc1; sb1 := dec_high 1 i.sb1|> = i'`; e(tac[]);
 e(elims);
 want `measure g i' < measure g i`; e(tac[]); 
 e(ssimp[measure_def]);
 have `? nts. nonterms_of_grammar g = nts`; e(tac[]);
 e(elims);
 e(SYM_TAC `_ = i'`);
 e(ssimp[]);
 e(ssimp[LET_THM]);
 e(MATCH_MP_TAC' SUM_MAP_LESS);
 cr();
  e(ssimp[]); 
  e(intros);
  e(Cases_on `nt' = nt`);
   e(ssimp[]);
   e(ssimp[listTheory.EXISTS_MEM,arith_simps]);
   e(tac[len_dec_high,less_le]);
 
   e(ssimp[]);
   have `len (dec_high 1 i.sb1) < len i.sb1`; e(tac[len_dec_high]);
   e(Cases_on `MEM (nt',dec_high 1 i.sb1) i.lc1` THEN ssimp[arith_simps]);
    e(tac[le_thms,less_le]);
   
    e(tac[le_thms,less_le]);

  (* ? nt'... *)
  er `nt`;
  e(ssimp[]);
  e(ssimp[arith_simps]);
  want `len (dec_high 1 i.sb1) < len i.sb1 + if MEM (nt,i.sb1) i.lc1 then 0 else 1`; e(INIT_TAC);
  e(tac[len_dec_high,le_thms,less_le]);
 
 (* ~ EXISTS *)
 val here_2365 = p(); dropn 1; add(here_2365);
 e(ssimp[LET_THM]);
 e(ssimp[listTheory.EVERY_MEM]);
 e(ssimp[update_lctxt_def]);
 want `measure g (i with lc1 := (nt,i.sb1)::i.lc1) < measure g i`; e(INIT_TAC); 
 e(ssimp[measure_def]);
 have `? nts. nonterms_of_grammar g = nts`; e(tac[]);
 e(elims);
 e(ssimp[LET_THM]);
 e(MATCH_MP_TAC' SUM_MAP_LESS);
 cr();
  e(intros);
  e(Cases_on `nt' = nt`);
   e(ssimp[arith_simps] THEN NO_TAC);

   e(ssimp[arith_simps] THEN NO_TAC);

  er `nt`;
  e(ssimp[arith_simps]);
val measure_less_measure = top_thm();

g `
(*EXISTS ($= (nt,sb)) lc1
==>*) len sb <> 0 /\ MEM nt (nonterms_of_grammar g)
==> measure g <|lc1 := (nt,dec_high 1 sb)::lc; sb1 := dec_high 1 sb|> < measure g <|lc1:=lc; sb1:=sb |>
`; 
e(intros);
(* what if (nt,dec_high 1 sb) is already in lc? but then nt in nonterms of grammar and length is less*)
e(Cases_on `MEM (nt,dec_high 1 sb) lc`);
 e(ssimp[]);
 e(ssimp[measure_def]);
 e(ssimp[LET_THM]);
 e(MATCH_MP_TAC' SUM_MAP_LESS);
 cr();
  e(intros);
  e(ssimp[]);
  e(Cases_on `nt' = nt` THEN ssimp[arith_simps]);
   e(tac[len_dec_high,le_thms,less_le]);

   e(Cases_on `MEM (nt',dec_high 1 sb) lc` THEN ssimp[arith_simps]);
    e(tac[len_dec_high,le_thms,less_le]);

    e(Cases_on `MEM (nt',sb) lc` THEN ssimp[arith_simps]);
     e(tac[len_dec_high,le_thms,less_le]);

     e(tac[len_dec_high,le_thms,less_le]);
  
  (* ? nt' *)
  er `nt`;  
  e(ssimp[arith_simps]);
  e(tac[len_dec_high,le_thms,less_le,arith_simps]);      

 (* ~ MEM *)
 val here_22635 = p(); dropn 1; add(here_22635);
 want `measure g <|lc1 := (nt,dec_high 1 sb)::lc; sb1 := dec_high 1 sb|> < measure g <|lc1:=lc;sb1:=sb|>`; e(INIT_TAC);
 e(ssimp[measure_def,LET_THM]);
 e(MATCH_MP_TAC' SUM_MAP_LESS);
 cr();
  e(intros);
  e(ssimp[]);
  e(Cases_on `nt' = nt` THEN ssimp[arith_simps]);
   e(tac[len_dec_high,le_thms,less_le]);

   e(Cases_on `MEM (nt',dec_high 1 sb) lc` THEN ssimp[arith_simps]);
    e(tac[len_dec_high,le_thms,less_le]);

    e(Cases_on `MEM (nt',sb) lc` THEN ssimp[arith_simps]);
     e(tac[len_dec_high,le_thms,less_le]);

     e(tac[len_dec_high,le_thms,less_le]);
  
  (* ? nt' *)
  er `nt`;  
  e(ssimp[arith_simps]);
  e(tac[len_dec_high,le_thms,less_le,arith_simps]);      
val measure_dec_high_less = top_thm();


g `
MEM nt (nonterms_of_grammar g)
==> EVERY ($~ o $= (nt,sb)) lc 
==> measure g <|lc1 := (nt,sb)::lc; sb1 := sb|> < measure g <| lc1:=lc; sb1:=sb |>
`;
e(intros);
e(ssimp[measure_def,LET_THM]);
e(MATCH_MP_TAC' SUM_MAP_LESS);
cr();
 e(intros);
 e(ssimp[]);
 e(Cases_on `nt' = nt` THEN ssimp[arith_simps] THEN tac[arith_simps]);

 (* ? nt' *)
 er `nt`;  
 e(ssimp[arith_simps]);
 e(Cases_on `MEM (nt,sb) lc` THEN ssimp[arith_simps]);
 e(ssimp[listTheory.EVERY_MEM] THEN NO_TAC);
val measure_cons_lc = top_thm();

(*   . proof: the incomprehensible proof *)


val gtp2_def = Define (*Hol_defn "gtp2"*) `
gtp2 p_of_tm g sym n i = case sym of
  TM tm -> ((p_of_tm tm) >> (\ v. LF(tm,v))) i || NT nt -> 
  if n = 0 then [] else
  let rules = FILTER (\ (nt',rhs). nt' = nt) g in 
  let alts1 = (FLAT o (MAP SND)) rules in 
  let alts2 = MAP (MAP (\ sym. gtp2 p_of_tm g sym (n-1))) alts1 in 
  let p = or_list (MAP (then_list2 nt) alts2) in 
  check_and_upd_lctxt nt p i 
`;

val gtp2_def_2 = rewrite_def gtp2_def ``sym:symbol``;

val _ = ``(gtp2:ty_p_of_tm -> grammar -> symbol -> num -> parse_tree parser)``;

val gtp1_def = Define `
gtp1 p_of_tm g sym i = gtp2 p_of_tm g sym (1+measure g i) i
`;


g `
l <> [] <=> ? x. MEM x l
`;
e(ssimp[]);
e(tac[listTheory.MEM,listTheory.NOT_NULL_MEM,listTheory.NULL_EQ]);
val NOT_NIL_EXISTS_MEM = top_thm();

g `
wf_p_of_tm p_of_tm /\ wf_grammar g ==> ! n sym i. suffix_sound (gtp2 p_of_tm g sym n)
`;
ir();
e(Induct_on `n`);
 e(Cases_on `sym`);
  e(ssimp[suffix_sound_def,gtp2_def_2]);
  e(intros);
  e(ssimp[]);
  e(intros);
  e(ssimp[myrr_def]);
  e(ssimp[listTheory.MEM_MAP]);
  e(ssimp[wf_p_of_tm_def,LET_THM]);
  e(Cases_on `y` THEN ssimp[]);
  e(tac[]); 

  e(ssimp[suffix_sound_def,gtp2_def_2] THEN NO_TAC);

 (* SUC *)
 e(intros);
 e(Cases_on `sym`);
  e(ssimp[suffix_sound_def,gtp2_def_2]);
  e(intros);
  e(ssimp[]);
  e(intros);
  e(ssimp[myrr_def]);
  e(ssimp[listTheory.MEM_MAP]);
  e(ssimp[wf_p_of_tm_def,LET_THM]);
  e(Cases_on `y` THEN ssimp[]);
  e(tac[]); 

  e(RENAME_TAC [``t:nonterm``|->``nt:nonterm``]);
  e(ssimp[suffix_sound_def,gtp2_def_2]);
  e(intros); 
  val here_3549 = p(); dropn 1; add(here_3549);
  e(ssimp[]);
  e(intros);
  e(elims);
  e(REORDER_TAC `MEM (pt,s_rem) _`);
  e(ssimp[LET_THM]);
  (* a nested induction; unfortunately we seem to have to do the case splits first *)
  val here_3402 = p(); dropn 1; add(here_3402);
  (* so we pull out the induction as a lemma *)
  have `
  ! nt lc alt pt s_rem s_tot.
  MEM (pt,s_rem) (then_list2 nt (MAP (\sym' a. gtp2 p_of_tm g sym' n a) alt) <|lc1 := lc; sb1 := s_tot|>) ==>
  ?s_pt. concatenate_two s_pt s_rem = SOME s_tot
  `;
   e(REMOVE_VAR_TAC `s_tot`); 
   ar(); ar();
   e(Induct_on `alt`);
    e(intros);
    e(ssimp[then_list_two_def,myrr_def]);
    e(ssimp[then_list_def_2,always_def]);
    e(ssimp[substr_def]);
    e(tac[exists_concatenate_two_equals]);
 
    (* cons *)
    val here_3487 = p(); dropn 1; add(here_3487);
    e(intros);
    e(RENAME_TAC [``h:symbol``|->``sym:symbol``]);
    e(REORDER_TAC `MEM (pt,s_rem) _`);
    e(assimp[then_list_two_def,myrr_def]0);
    e(ssimp[listTheory.MEM_MAP]);   
    e(Cases_on `y` THEN ssimp[]);
    e(SYM_TAC `s_rem = _`);
    e(ssimp[]);   
    e(RENAME_TAC [``q:parse_tree list``|->``pts:parse_tree list``]);
    e(Cases_on `pts`);
     e(ssimp[then_list_def_2,myrr_def,listTheory.MEM_MAP]);
     e(Cases_on `y` THEN ssimp[]);
     e(Cases_on `q` THEN ssimp[] THEN NO_TAC);
    e(REMOVE_VAR_TAC `pt`);
    e(RENAME_TAC [``h:parse_tree``|->``pt:parse_tree``,``t:parse_tree list``|->``pts:parse_tree list``]);
    have `? s_rem'. MEM (pt,s_rem') ((\ a. gtp2 p_of_tm g sym n a) <|lc1 := lc; sb1 := s_tot|>) /\ MEM (pts,s_rem) (then_list (MAP (\ sym' a. gtp2 p_of_tm g sym' n a) alt) <|lc1 := lc; sb1 := s_rem'|>)`; 
     e(tac[MEM_cons_then_list]);
    e(elims);
    xal `sym`;
    xal `lc`;
    xal `s_tot`;
    e(ssimp[]);
    xal `pt`;
    xal `s_rem'`;
    il 0; e(ssimp[] THEN NO_TAC);
    e(elims);
    have `concatenate_two s_pt s_rem' = SOME s_tot`; e(INIT_TAC);
    want `? s_pt. concatenate_two s_pt s_rem = SOME s_tot`; e(INIT_TAC);
    xal `NODE(nt,pts)`;
    xal `s_rem`;
    xal `s_rem'`;
    il 0;
     e(ssimp[then_list_two_def,myrr_def]);
     e(ssimp[listTheory.MEM_MAP]);
     er `(pts,s_rem)`;
     e(ssimp[] THEN NO_TAC);
    e(elims);
    e(RENAME_TAC [``s_pt':substring``|->``s_pts:substring``]);
    have `concatenate_two s_pts s_rem = SOME s_rem'`; e(INIT_TAC);
    e(elims);
    val here_3529 = p(); dropn 1; add(here_3529);
    (* want s_rem suffix of s_tot; have s_rem suffix of s_rem', s_rem' suffix of s_tot *)
    e(MY_ASSUME_TAC(INST [``s:substring``|->``s_pt:substring``] tcases_2));
    e(elims);
    e(MY_ASSUME_TAC(INST [``s:substring``|->``s_pts:substring``] tcases_2));
    e(elims);
    er `myabs (a, b, c')`;
    e(MY_ASSUME_TAC(INST [``s:substring``|->``s_tot:substring``] tcases_2));
    e(elims);
    e(MY_ASSUME_TAC(INST [``s:substring``|->``s_rem:substring``] tcases_2));
    e(elims);
    e(MY_ASSUME_TAC(INST [``s:substring``|->``s_rem':substring``] tcases_2));
    e(elims);
    e(ssimp[concatenate_two_def]);
    e(ssimp[inc_high_def,low_def,high_def,dec_high_def,string_def,len_def,LET_THM]);
    e(ssimp ty_substring_simps);
    have `wf_substring (a'''',b,c'''') /\ wf_substring (a''',b',c''')`; e(tac[wf_substring_thms]);
    e(ssimp ty_substring_simps);
    have `wf_substring (a'',b'',b''')`; e(tac[wf_substring_thms]);
    e(ssimp ty_substring_simps THEN NO_TAC);
    (* end of induction lemma *)
  val here_3488 = p(); dropn 1; add(here_3488);
  e(ssimp[check_and_upd_lctxt_def]);
  e(Cases_on `EXISTS ($= (nt,s_tot)) lc`);
   e(ssimp[LET_THM]);
   e(Cases_on `len s_tot = 0`); e(ssimp[] THEN NO_TAC); 
   e(ssimp[]);
   e(ssimp[ignr_last_def]);
   e(ssimp[substr_def,LET_THM]);
   e(ssimp[listTheory.MEM_MAP]);
   e(Cases_on `y` THEN ssimp[]);
   e(SYM_TAC `pt = _`);
   e(ssimp[]);
   e(ssimp[update_lctxt_def]);
   e(REMOVE_VARS_TAC [`q`,`s_rem`]);
   e(RENAME_TAC [``r:substring``|->``s_rem:substring``]);
   e(ssimp[lift_def]);
   have `? i. <|lc1 := (nt,dec_high 1 s_tot)::lc; sb1 := dec_high 1 s_tot|> = i`; e(tac[]);
   e(elims);
   e(ssimp[arith_simps]);
   e(ssimp[SYM(SPEC_ALL or_list_thm)]);
   e(ssimp[listTheory.MEM_MAP]);
   e(RENAME_TAC [``y':symbol list``|->``alt:symbol list``]);
   e(ssimp[]);
   e(REMOVE_VARS_TAC [`p`,`y`]);
   have `? s_pt. concatenate_two s_pt s_rem = SOME (dec_high 1 s_tot)`; e(tac[]);
   e(elims);
   want `? s_pt. concatenate_two s_pt (inc_high 1 s_rem) = SOME s_tot`; e(INIT_TAC);
   er `s_pt`;
   e(ssimp[]);
   e(MY_ASSUME_TAC(INST [``s:substring``|->``s_pt:substring``] tcases_2));
   e(elims);
   e(MY_ASSUME_TAC(INST [``s:substring``|->``s_rem:substring``] tcases_2));
   e(elims);
   e(MY_ASSUME_TAC(INST [``s:substring``|->``s_tot:substring``] tcases_2));
   e(elims);
   e(ssimp[concatenate_two_def,dec_high_def,inc_high_def,string_def,low_def,high_def,len_def,LET_THM]);
   e(ssimp ty_substring_simps);
   have `wf_substring (a',b,c') /\ wf_substring (a'',b'',c'' - 1)`; e(tac[wf_substring_thms]);
   e(ssimp ty_substring_simps);
   have `c'' - 1 + 1 = c''`; 
    e(Q.PAT_UNDISCH_TAC `c'' - b'' <> 0`);   
    e(numLib.ARITH_TAC);
   e(ssimp[]);
   e(ssimp ty_substring_simps);
   have `wf_substring (a'',b',c'')`; e(tac[wf_substring_thms]);
   e(ssimp ty_substring_simps THEN NO_TAC);

   (* ~ EXISTS *)
   val here_3548 = p(); dropn 1; add(here_3548);
   e(ssimp[LET_THM]);
   e(ssimp[update_lctxt_def]);
   e(ssimp[arith_simps]);
   e(ssimp[SYM(SPEC_ALL or_list_thm)]);
   e(ssimp[listTheory.MEM_MAP]);
   e(RENAME_TAC [``y':symbol list``|->``alt:symbol list``]);
   e(ssimp[]);
   e(REMOVE_VARS_TAC [`p`,`y`]);
   e(tac[]);
val suffix_sound_gtp2 = top_thm(); 
    

(* show that the n argument can be syntactically eliminated in gtp2 *)
g `
! n. ! sym i.
(measure g i < n) ==> ( 
gtp2 p_of_tm g sym n i = case sym of
  TM tm -> ((p_of_tm tm) >> (\ v. LF(tm,v))) i || NT nt -> 
  let rules = FILTER (\ (nt',rhs). nt' = nt) g in 
  let alts1 = (FLAT o (MAP SND)) rules in 
  let alts2 = MAP (MAP (\ sym. gtp2 p_of_tm g sym (n-1))) alts1 in 
  let p = or_list (MAP (then_list2 nt) alts2) in 
  check_and_upd_lctxt nt p i)
`;
e(intros);
e(Cases_on `sym`);
 e(ssimp[]);
 e(ssimp[gtp2_def_2] THEN NO_TAC);

 e(RENAME_TAC [``t:nonterm``|->``nt:nonterm``]);
 e(ssimp[gtp2_def_2]);
 e(Cases_on `n=0`);
  e(ssimp[arith_simps] THEN NO_TAC);
  
  e(ssimp[]);
  have `(\sym' a. gtp2 p_of_tm g sym' (n - 1) a) = (\sym. gtp2 p_of_tm g sym (n - 1))`; e(tac[]);
  e(ssimp[] THEN NO_TAC);
val tmp2 = top_thm();

g `
wf_p_of_tm p_of_tm /\ wf_grammar g
==> ! n. ! sym. ! i. measure g i < n ==> (gtp2 p_of_tm g sym n i = gtp2 p_of_tm g sym (1+measure g i) i)
`;
ir();
e(completeInduct_on `n`);
e(intros);
e(ASM_SIMP_TAC (srw_ss()) [tmp2,arith_simps]);
e(Cases_on `sym` THEN ssimp[]);
e(ssimp[LET_THM]);
e(RENAME_TAC [``t:nonterm``|->``nt:nonterm``]);
have `? rules. FILTER (\ (nt',rhs). nt' = nt) g = rules`; e(tac[]); 
e(elims);
have `? alts1. FLAT (MAP SND rules) = alts1`; e(tac[]);
e(elims);
e(ssimp[]);
have `? alts2. MAP (MAP (\ sym. gtp2 p_of_tm g sym (n-1))) alts1 = alts2`; e(tac[]);
have `? alts2'. MAP (MAP (\ sym. gtp2 p_of_tm g sym (measure g i))) alts1 = alts2'`; e(tac[]);
e(elims);
e(ssimp[LET_THM]);
e(ssimp[arith_simps]);
want `check_and_upd_lctxt nt (or_list (MAP (then_list2 nt) alts2)) i = check_and_upd_lctxt nt (or_list (MAP (then_list2 nt) alts2')) i`; e(INIT_TAC);
e(ssimp[check_and_upd_lctxt_def]); 
e(Cases_on `EXISTS ($= (nt,i.sb1)) i.lc1`);
 e(ssimp[]);
 e(Cases_on `len i.sb1 = 0`);
  e(ssimp[]);
  e(ssimp[LET_THM] THEN NO_TAC);

  val here_22364 = p(); dropn 1; add(here_22364);
  e(ssimp[LET_THM]);
  e(ssimp[ignr_last_def]);
  e(ssimp[substr_def]);
  e(ssimp[LET_THM]); 
  e(MATCH_MP_TAC' listTheory.MAP_CONG);
  cr(); defer(); e(tac[]);
  e(ssimp[update_lctxt_def]);
  have `? lc sb. i = <| lc1 := lc; sb1 := sb |>`; e(tac[icases_thm]);
  e(ssimp[]); 
  e(ssimp[lift_def]);
  e(SYM_TAC `_ = alts2`);
  e(SYM_TAC `_ = alts2'`);
  e(ssimp[]);       
  e(SIMP_TAC std_ss [rich_listTheory.MAP_MAP_o]);
  e(MATCH_MP_TAC' or_list_cong);   
  e(intros);
  e(ssimp[]);
  e(RENAME_TAC [``x:symbol list``|->``alt:symbol list``]);
  e(ssimp[then_list_two_def]);
  want `
  (then_list (MAP (\sym. gtp2 p_of_tm g sym (n-1)) alt)) <|lc1 := (nt,dec_high 1 sb)::lc; sb1 := dec_high 1 sb|>
  = (then_list (MAP (\sym. gtp2 p_of_tm g sym (measure g <|lc1 := lc; sb1:=sb|>)) alt)) <|lc1 := (nt,dec_high 1 sb)::lc; sb1 := dec_high 1 sb|>
  `; 
   e(ssimp[myrr_def] THEN NO_TAC);
  (* and this depends on the fact that the strings get shorter *)
  val here_22580 = p(); dropn 1; add(here_22580);
  have `MEM nt (nonterms_of_grammar g)`; 
   have `rules <> []`;
    ir();
    e(SYM_TAC `_ = alts1`);
    e(ssimp[] THEN NO_TAC);
   have `? rhs. MEM (nt,rhs) g`; 
    e(Cases_on `rules` THEN ssimp[]);
    e(Cases_on `h` THEN ssimp[]);
    er `r`;
    have `MEM (q,r) (FILTER (\ (nt',rhs). nt' = nt) g)`;
     e(ssimp[] THEN NO_TAC);
    e(assimp[listTheory.MEM_FILTER]0);
    e(tac[]);
   e(ssimp[nonterms_of_grammar_def]);
   e(ssimp[listTheory.MEM_MAP]);
   er `NT nt`;
   e(ssimp[dest_NT_def]);
   e(ssimp[listTheory.MEM_FILTER]);
   e(ssimp[is_NT_def]); 
   e(ssimp[symbols_of_grammar_def]);
   e(ssimp[listTheory.MEM_FLAT]);
   er `symbols_of_parse_rule (nt,rhs)`;
   e(ssimp[listTheory.MEM_MAP]);
   cr();
    er `(nt,rhs)`;
    e(ssimp[] THEN NO_TAC);

    e(ssimp[symbols_of_parse_rule_def] THEN NO_TAC);
  (* goal as easlier want *)
  have `measure g <|lc1 := (nt,dec_high 1 sb)::lc; sb1 := dec_high 1 sb|> < measure g i`; e(tac[measure_dec_high_less]);
  val here_2931 = p(); dropn 1; add(here_2931);
  want `
  then_list (MAP (\ sym. gtp2 p_of_tm g sym (n - 1)) alt) <|lc1 := (nt,dec_high 1 sb)::lc; sb1 := dec_high 1 sb|> =
  then_list (MAP (\ sym. gtp2 p_of_tm g sym (measure g <|lc1 := lc; sb1 := sb|>)) alt) <|lc1 := (nt,dec_high 1 sb)::lc; sb1 := dec_high 1 sb|>
  `; e(INIT_TAC);
  e(MATCH_MP_TAC' then_list_cong);
  cr(); e(tac[suffix_sound_gtp2]);
  cr(); e(tac[suffix_sound_gtp2]);
  e(intros);
  e(ssimp[]);
  have `measure g <|lc1 := (nt,dec_high 1 sb)::lc; sb1 := s_rem|> < measure g <|lc1 := lc; sb1 := sb|>`; 
   have `measure g <|lc1 := (nt,dec_high 1 sb)::lc; sb1 := dec_high 1 sb|> < measure g <|lc1 := lc; sb1 := sb|>`;
    e(MATCH_MP_TAC' measure_dec_high_less);
    e(ssimp[]);
   have `(s_rem = dec_high 1 sb) \/ (len s_rem < len (dec_high 1 sb))`; e(tac[concatenate_two_SOME]);
   dl(); 
    e(tac[]);

    have `measure g <|lc1 := (nt,dec_high 1 sb)::lc; sb1 := s_rem|> <= measure g <|lc1 := (nt,dec_high 1 sb)::lc; sb1 := dec_high 1 sb|>`;
     e(MATCH_MP_TAC' measure_substring);
     e(INIT_TAC);
    have `! x y z. x <= y /\ y < z ==> x < z`; e(numLib.ARITH_TAC);
    e(tac[]);
  al `n-1`;
  il 0; 
   want `n-1 < n`; e(INIT_TAC);
   have `? x. x < n`; e(tac[]);
   e(elims);
   e(Q.PAT_UNDISCH_TAC `x' < n`);
   e(numLib.ARITH_TAC);
  xal `x`;
  xal `<|lc1 := (nt,dec_high 1 sb)::lc; sb1 := s_rem|>`;
  il 0;
   want `measure g <|lc1 := (nt,dec_high 1 sb)::lc; sb1 := s_rem|> < n - 1`; e(INIT_TAC);
   have `measure g i < n`; e(tac[]);
   have `! x y z. x < y /\ y < z ==> x < z - 1`; e(numLib.ARITH_TAC);
   e(tac[]);
  xal `measure g i`;
  il 0; e(tac[]);
  xal `x`;
  xal `<|lc1 := (nt,dec_high 1 sb)::lc; sb1 := s_rem|>`;
  il 0; e(tac[]);
  e(ssimp[] THEN NO_TAC);
  
 (* ~ EXISTS *)
 val here_22662 = p(); dropn 1; add(here_22662);
 e(simp[]);
 e(ssimp[LET_THM]);
 have `? lc sb. i = <| lc1 := lc; sb1 := sb |>`; e(tac[icases_thm]);
 e(ssimp[]); 
 e(ssimp[update_lctxt_def]);
 e(SYM_TAC `_ = alts2`);
 e(SYM_TAC `_ = alts2'`);
 e(ssimp[]);       
 e(SIMP_TAC std_ss [rich_listTheory.MAP_MAP_o]);
 e(MATCH_MP_TAC' or_list_cong);   
 e(intros);
 e(ssimp[]);
 e(RENAME_TAC [``x:symbol list``|->``alt:symbol list``]);
 have `MEM nt (nonterms_of_grammar g)`; 
  have `rules <> []`;
   ir();
   e(SYM_TAC `_ = alts1`);
   e(ssimp[] THEN NO_TAC);
  have `? rhs. MEM (nt,rhs) g`; 
   e(Cases_on `rules` THEN ssimp[]);
   e(Cases_on `h` THEN ssimp[]);
   er `r`;
   have `MEM (q,r) (FILTER (\ (nt',rhs). nt' = nt) g)`;
    e(ssimp[] THEN NO_TAC);
   e(assimp[listTheory.MEM_FILTER]0);
   e(tac[]);
  e(ssimp[nonterms_of_grammar_def]);
  e(ssimp[listTheory.MEM_MAP]);
  er `NT nt`;
  e(ssimp[dest_NT_def]);
  e(ssimp[listTheory.MEM_FILTER]);
  e(ssimp[is_NT_def]); 
  e(ssimp[symbols_of_grammar_def]);
  e(ssimp[listTheory.MEM_FLAT]);
  er `symbols_of_parse_rule (nt,rhs)`;
  e(ssimp[listTheory.MEM_MAP]);
  cr();
   er `(nt,rhs)`;
   e(ssimp[] THEN NO_TAC);

   e(ssimp[symbols_of_parse_rule_def] THEN NO_TAC);
 e(ssimp[then_list_two_def]);
 val here_3955 = p(); dropn 1; add(here_3955);
 want `
 (then_list (MAP (\sym. gtp2 p_of_tm g sym (n - 1)) alt) ) <|lc1 := (nt,sb)::lc; sb1 := sb|> =
 (then_list (MAP (\sym. gtp2 p_of_tm g sym (measure g <|lc1 := lc; sb1 := sb|>)) alt) ) <|lc1 := (nt,sb)::lc; sb1 := sb|>
 `;
  e(ssimp[myrr_def] THEN NO_TAC);
 e(MATCH_MP_TAC' then_list_cong);
 cr(); e(tac[suffix_sound_gtp2]);
 cr(); e(tac[suffix_sound_gtp2]);
 e(intros);
 e(ssimp[]);
 have `measure g <|lc1 := (nt,sb)::lc; sb1 := s_rem|> < measure g <|lc1 := lc; sb1 := sb|>`; 
  have `measure g <|lc1 := (nt,sb)::lc; sb1 := sb|> < measure g <|lc1 := lc; sb1 := sb|>`; 
   e(MATCH_MP_TAC' measure_cons_lc);
   e(tac[]);
  have `(s_rem = sb) \/ (len s_rem < len sb)`; e(tac[concatenate_two_SOME]);
  dl(); 
   e(tac[]);

   have `measure g <|lc1 := (nt,sb)::lc; sb1 := s_rem|> <= measure g <|lc1 := (nt,sb)::lc; sb1 := sb|>`;
    e(MATCH_MP_TAC' measure_substring);
    e(INIT_TAC);
   have `! x y z. x <= y /\ y < z ==> x < z`; e(numLib.ARITH_TAC);
   e(tac[]);
 al `n-1`;
 il 0; 
  want `n-1 < n`; e(INIT_TAC);
   have `? x. x < n`; e(tac[]);
   e(elims);
   e(Q.PAT_UNDISCH_TAC `x' < n`);
   e(numLib.ARITH_TAC);
 xal `x`;
 xal `<|lc1 := (nt,sb)::lc; sb1 := s_rem|>`;
 il 0;
  want `measure g <|lc1 := (nt,sb)::lc; sb1 := s_rem|> < n - 1`; e(INIT_TAC);
  have `measure g i < n`; e(tac[]);
  have `! x y z. x < y /\ y < z ==> x < z - 1`; e(numLib.ARITH_TAC);
  e(tac[]);
 xal `measure g i`;
 il 0; e(tac[]);
 xal `x`;
 xal `<|lc1 := (nt,sb)::lc; sb1 := s_rem|>`;
 il 0; e(tac[]);
 e(ssimp[] THEN NO_TAC);
val measure_gtp2_agrees = top_thm();

(* show that gtp1 agrees with gtp2; an easy subst gives that gtp1 obeys the right recursion *)
g `
wf_p_of_tm p_of_tm /\ wf_grammar g
==> (gtp1 p_of_tm g sym i = case sym of
  TM tm -> ((p_of_tm tm) >> (\ v. LF(tm,v))) i || NT nt -> 
  let rules = FILTER (\ (nt',rhs). nt' = nt) g in 
  let alts1 = (FLAT o (MAP SND)) rules in 
  let alts2 = MAP (MAP (\ sym i. gtp2 p_of_tm g sym (1+(measure g i)) i)) alts1 in 
  let p = or_list (MAP (then_list2 nt) alts2) in 
  check_and_upd_lctxt nt p i)
`;
ir();
e(ssimp[gtp1_def]);
have `measure g i < 1+measure g i`; e(ssimp[arith_simps] THEN NO_TAC);
e(Cases_on `sym`);
 e(ssimp[tmp2] THEN NO_TAC);
 
 e(ssimp[]);
 e(ssimp[gtp2_def_2]);
 e(RENAME_TAC [``t:nonterm``|->``nt:nonterm``]);
 have `? rules. FILTER (\ (nt',rhs). nt' = nt) g = rules`; e(tac[]); 
 e(elims);
 have `? alts1. FLAT (MAP SND rules) = alts1`; e(tac[]);
 e(elims);
 e(ssimp[]);
 have `? alts2. MAP (MAP (\ sym' a. gtp2 p_of_tm g sym' (measure g i) a)) alts1 = alts2`; e(tac[]);
 have `? alts2'. MAP (MAP (\ sym i. gtp2 p_of_tm g sym (1+measure g i) i)) alts1 = alts2'`; e(tac[]);
 e(elims);
 e(ssimp[LET_THM,arith_simps]);
 want `check_and_upd_lctxt nt (or_list (MAP (then_list2 nt) alts2)) i = check_and_upd_lctxt nt (or_list (MAP (then_list2 nt) alts2')) i`; e(INIT_TAC);
 want `! i'. ! alt. MEM alt alts1 /\ measure g i' < measure g i ==> (
   (then_list (MAP (\sym' a. gtp2 p_of_tm g sym' (measure g i) a) alt)) i'
   = (then_list (MAP (\sym i. gtp2 p_of_tm g sym (1 + measure g i) i) alt)) i')
 `;
  e(ssimp[check_and_upd_lctxt_def]); 
  e(Cases_on `EXISTS ($= (nt,i.sb1)) i.lc1`);
   e(ssimp[]);
   e(Cases_on `len i.sb1 = 0`);
    e(ssimp[]);
    e(ssimp[LET_THM] THEN NO_TAC);
 
    val here_2364 = p(); dropn 1; add(here_2364);
    e(ssimp[LET_THM]);
    e(ssimp[ignr_last_def]);
    e(ssimp[substr_def]);
    e(ssimp[LET_THM]); 
    e(MATCH_MP_TAC' listTheory.MAP_CONG);
    cr(); defer(); e(tac[]);
    e(ssimp[update_lctxt_def]);
    have `? lc sb. i = <| lc1 := lc; sb1 := sb |>`; e(tac[icases_thm]);
    e(ssimp[]); 
    e(ssimp[lift_def]);
    e(SYM_TAC `_ = alts2`);
    e(SYM_TAC `_ = alts2'`);
    e(ssimp[]);       
    e(SIMP_TAC std_ss [rich_listTheory.MAP_MAP_o]);
    e(MATCH_MP_TAC' or_list_cong);   
    e(intros);
    e(ssimp[]);
    e(RENAME_TAC [``x:symbol list``|->``alt:symbol list``]);
    e(ssimp[then_list_two_def]);
    want `
    (then_list (MAP (\sym' a. gtp2 p_of_tm g sym' (measure g <|lc1 := lc; sb1 := sb|>) a) alt)) <|lc1 := (nt,dec_high 1 sb)::lc; sb1 := dec_high 1 sb|>
    = (then_list (MAP (\sym i. gtp2 p_of_tm g sym (1 + measure g i) i) alt)) <|lc1 := (nt,dec_high 1 sb)::lc; sb1 := dec_high 1 sb|>
    `; 
     e(ssimp[myrr_def] THEN NO_TAC);
    (* and this depends on the fact that the strings get shorter *)
    val here_2580 = p(); dropn 1; add(here_2580);
    have `MEM nt (nonterms_of_grammar g)`; 
     have `rules <> []`;
      ir();
      e(SYM_TAC `_ = alts1`);
      e(ssimp[] THEN NO_TAC);
     have `? rhs. MEM (nt,rhs) g`; 
      e(Cases_on `rules` THEN ssimp[]);
      e(Cases_on `h` THEN ssimp[]);
      er `r`;
      have `MEM (q,r) (FILTER (\ (nt',rhs). nt' = nt) g)`;
       e(ssimp[] THEN NO_TAC);
      e(assimp[listTheory.MEM_FILTER]0);
      e(tac[]);
     e(ssimp[nonterms_of_grammar_def]);
     e(ssimp[listTheory.MEM_MAP]);
     er `NT nt`;
     e(ssimp[dest_NT_def]);
     e(ssimp[listTheory.MEM_FILTER]);
     e(ssimp[is_NT_def]); 
     e(ssimp[symbols_of_grammar_def]);
     e(ssimp[listTheory.MEM_FLAT]);
     er `symbols_of_parse_rule (nt,rhs)`;
     e(ssimp[listTheory.MEM_MAP]);
     cr();
      er `(nt,rhs)`;
      e(ssimp[] THEN NO_TAC);
  
      e(ssimp[symbols_of_parse_rule_def] THEN NO_TAC);
    (* goal as easlier want *)
    have `measure g <|lc1 := (nt,dec_high 1 sb)::lc; sb1 := dec_high 1 sb|> < measure g i`; e(tac[measure_dec_high_less]);
    e(tac[]);

   (* ~ EXISTS *)
   val here_2662 = p(); dropn 1; add(here_2662);
   e(simp[]);
   e(ssimp[LET_THM]);
   have `? lc sb. i = <| lc1 := lc; sb1 := sb |>`; e(tac[icases_thm]);
   e(ssimp[]); 
   e(ssimp[update_lctxt_def]);
   e(SYM_TAC `_ = alts2`);
   e(SYM_TAC `_ = alts2'`);
   e(ssimp[]);       
   e(SIMP_TAC std_ss [rich_listTheory.MAP_MAP_o]);
   e(MATCH_MP_TAC' or_list_cong);   
   e(intros);
   e(ssimp[]);
   e(RENAME_TAC [``x:symbol list``|->``alt:symbol list``]);
   have `MEM nt (nonterms_of_grammar g)`; 
    have `rules <> []`;
     ir();
     e(SYM_TAC `_ = alts1`);
     e(ssimp[] THEN NO_TAC);
    have `? rhs. MEM (nt,rhs) g`; 
     e(Cases_on `rules` THEN ssimp[]);
     e(Cases_on `h` THEN ssimp[]);
     er `r`;
     have `MEM (q,r) (FILTER (\ (nt',rhs). nt' = nt) g)`;
      e(ssimp[] THEN NO_TAC);
     e(assimp[listTheory.MEM_FILTER]0);
     e(tac[]);
    e(ssimp[nonterms_of_grammar_def]);
    e(ssimp[listTheory.MEM_MAP]);
    er `NT nt`;
    e(ssimp[dest_NT_def]);
    e(ssimp[listTheory.MEM_FILTER]);
    e(ssimp[is_NT_def]); 
    e(ssimp[symbols_of_grammar_def]);
    e(ssimp[listTheory.MEM_FLAT]);
    er `symbols_of_parse_rule (nt,rhs)`;
    e(ssimp[listTheory.MEM_MAP]);
    cr();
     er `(nt,rhs)`;
     e(ssimp[] THEN NO_TAC);
 
     e(ssimp[symbols_of_parse_rule_def] THEN NO_TAC);
   e(ssimp[then_list_two_def]);
   want `
 (then_list (MAP (\sym' a. gtp2 p_of_tm g sym' (measure g <|lc1 := lc; sb1 := sb|>) a) alt))
   <|lc1 := (nt,sb)::lc; sb1 := sb|> =
 (then_list (MAP (\sym i. gtp2 p_of_tm g sym (1 + measure g i) i) alt))
   <|lc1 := (nt,sb)::lc; sb1 := sb|>
   `;
    e(ssimp[myrr_def] THEN NO_TAC);
   have `measure g <|lc1 := (nt,sb)::lc; sb1 := sb|> < measure g i`; e(tac[measure_cons_lc]);
   e(tac[]);

 (* goal change! *)
 val here_2728 = p(); dropn 1; add(here_2728);
 e(intros);
 e(elims);
 have `? lc sb. i' = <| lc1 := lc; sb1 := sb |>`; e(tac[icases_thm]);
 e(elims);
 e(ssimp[]); 
 e(MATCH_MP_TAC' then_list_cong);
 cr(); e(tac[suffix_sound_gtp2]);
 cr(); 
  e(intros);
  e(ssimp[]);
  e(MY_ASSUME_TAC suffix_sound_gtp2);
  il 0; e(tac[]);
  e(ssimp[suffix_sound_def]);
  e(tac[]); (* some eta expansion necessary e(tac[suffix_sound_gtp2]); *)
 e(intros);
 e(elims);
 e(ssimp[]);
 have `(s_rem = sb) \/ len s_rem < len sb`; 
  e(tac[concatenate_two_SOME]);
 dl();
  e(ssimp[]);
  (* just use the fact that gtp2 is given a size argument bigger than the measure of the input arg *)
  e(ssimp[measure_gtp2_agrees] THEN NO_TAC);

  e(ssimp[]);
  have `measure g <| lc1:=lc; sb1:=s_rem |> <= measure g <| lc1:=lc; sb1:=sb |>`; e(tac[measure_substring]);
  have `measure g <| lc1:=lc; sb1:=s_rem |> < measure g i`; e(tac[le_thms,less_le]);
  (* and again use the fact that gtp2 is constant is size arg bigger than measure *)
  e(ssimp[measure_gtp2_agrees] THEN NO_TAC);
val tmp3 = top_thm(); (* Phew! *)


g `
wf_p_of_tm p_of_tm /\ wf_grammar g
==> (gtp1 p_of_tm g sym i = case sym of
  TM tm -> ((p_of_tm tm) >> (\ v. LF(tm,v))) i || NT nt -> 
  let rules = FILTER (\ (nt',rhs). nt' = nt) g in 
  let alts1 = (FLAT o (MAP SND)) rules in 
  let alts2 = MAP (MAP (\ sym. gtp1 p_of_tm g sym)) alts1 in 
  let p = or_list (MAP (then_list2 nt) alts2) in 
  check_and_upd_lctxt nt p i)
`;
have `(\ sym i. gtp2 p_of_tm g sym (1+(measure g i)) i) = (\ sym. gtp1 p_of_tm g sym)`;
 e(MATCH_MP_TAC' EQ_EXT);
 e(intros);
 e(ssimp[]);
 e(MATCH_MP_TAC' EQ_EXT);
 e(ssimp[]);
 e(ssimp[gtp1_def] THEN NO_TAC);
e(MY_ASSUME_TAC tmp3);
e(ssimp[] THEN NO_TAC);
val tmp4 = top_thm();

g `
? gtp1. 
! p_of_tm g sym i.
wf_p_of_tm p_of_tm /\ wf_grammar g
==> (gtp1 p_of_tm g sym i = case sym of
  TM tm -> ((p_of_tm tm) >> (\ v. LF(tm,v))) i || NT nt -> 
  let rules = FILTER (\ (nt',rhs). nt' = nt) g in 
  let alts1 = (FLAT o (MAP SND)) rules in 
  let alts2 = MAP (MAP (\ sym. gtp1 p_of_tm g sym)) alts1 in 
  let p = or_list (MAP (then_list2 nt) alts2) in 
  check_and_upd_lctxt nt p i)
`;
e(tac[tmp4]);
val exists_gtp1 = top_thm();

(* * grammar_to_parser defn *)

val grammar_to_parser_def = new_specification ("grammar_to_parser_def", ["grammar_to_parser"], exists_gtp1);

val grammar_to_parser_def_2 = SIMP_RULE (srw_ss()) [] (INST [``i:ty_input``|->``<| lc1 := lc; sb1 := s |>``] (SPEC_ALL grammar_to_parser_def));


(* * defn of theorems *)

val admits_thm_def = Define `
admits_thm = ! pt. wf_parse_tree pt ==> good_tree pt ==> admits [] pt
`;

val good_tree_exists_thm_def = Define `
good_tree_exists_thm = ! ss_of_tm. ! g. ! pt. ? pt'.
  pt IN (pts_of ss_of_tm g)
  ==> pt' IN (pts_of ss_of_tm g) /\ (matches_pt pt pt') /\ (good_tree pt')
`;

val prefix_sound_sound_thm_def = Define `
prefix_sound_sound_thm = ! ss_of_tm. ! g. ! sym. ! p.
  prefix_sound ss_of_tm g sym p ==> sound ss_of_tm g sym (simple_parser_of p)
`;

val prefix_complete_complete_thm_def = Define `
prefix_complete_complete_thm = ! ss_of_tm. ! g. ! sym. ! p.
  prefix_complete ss_of_tm g sym p ==> complete ss_of_tm g sym (simple_parser_of p)
`;

val prefix_sound_grammar_to_parser_thm_def = Define `
prefix_sound_grammar_to_parser_thm = ! p_of_tm. ! g. ! sym.
  let p = grammar_to_parser p_of_tm g sym in
  let ss_of_tm = ss_of_tm_of p_of_tm in
  wf_p_of_tm p_of_tm /\ wf_grammar g ==> prefix_sound ss_of_tm g sym p
`;

val sound_grammar_to_parser_thm_def = Define `
sound_grammar_to_parser_thm = ! p_of_tm. ! g. ! sym.
  let p = grammar_to_parser p_of_tm g sym in
  let ss_of_tm = ss_of_tm_of p_of_tm in
  wf_p_of_tm p_of_tm /\ wf_grammar g ==> sound ss_of_tm g sym (simple_parser_of p)
`;


val main_thm_def = Define `
main_thm = ! p_of_tm. ! g. ! pt. ! sym. ! s_pt. ! s_rem. ! s_tot. ! lc.
  let p = grammar_to_parser p_of_tm g sym in
  let ss_of_tm = ss_of_tm_of p_of_tm in
  wf_p_of_tm p_of_tm
  /\ wf_grammar g
  /\ wf_parse_tree pt
  /\ pt IN (pts_of ss_of_tm g)
  /\ (root pt = sym)
  /\ (substring_of pt = SOME s_pt) (* s_pt is wf_substring anyway *)
  /\ (concatenate_two s_pt s_rem = SOME s_tot) (* /\ good_tree pt *)
  /\ admits lc pt
  ==>
  MEM (pt,s_rem) (p <| lc1 := lc; sb1 := s_tot |>)
`;


(* FIXME why not p rather than (p nt)? FIXME typing *)

(* FIXME need to sort out nts and syms *)

val corollary_def = Define `
corollary = ! p_of_tm. ! g. ! sym.
  let ss_of_tm = ss_of_tm_of p_of_tm in
  let p = grammar_to_parser p_of_tm g sym in
  wf_p_of_tm p_of_tm /\ wf_grammar g ==> prefix_complete ss_of_tm g sym p
`;

(* FIXME why (p nt) rather than p? *)
val complete_grammar_to_parser_thm_def = Define `
complete_grammar_to_parser_thm = ! p_of_tm. ! g. ! sym.
  let ss_of_tm = ss_of_tm_of p_of_tm in
  let p = grammar_to_parser p_of_tm g sym in
  wf_p_of_tm p_of_tm /\ wf_grammar g 
  ==> complete ss_of_tm g sym (simple_parser_of p)
`;

(* * proof *)
(*  + check_and_upd_lctxt lemmas *)

g `
MEM (pt,s_rem) (check_and_upd_lctxt nt p <|lc1 := lc; sb1 := s_tot|>)
==> ? lc' s_rem' s_tot'. MEM (pt,s_rem') (p <|lc1 := lc'; sb1 := s_tot'|>) (* /\ (wf_substring s_tot ==> wf_substring s_tot') *)
`;
e(intros);
e(ssimp[check_and_upd_lctxt_def]);
e(Cases_on `EXISTS ($= (nt,s_tot)) lc` THEN ssimp[LET_THM]);
 e(Cases_on `len s_tot = 0` THEN ssimp[]);
 e(ssimp[ignr_last_def,update_lctxt_def]);
 e(ssimp[substr_def,LET_THM]);
 e(ssimp[listTheory.MEM_MAP]);
 e(ssimp[lift_def,dec_high_def]);
 e(Cases_on `y` THEN ssimp[]);
 (*
 have `(* wf_substring s_tot ==> *) wf_substring (dec_high 1 s_tot)`; 
  ir();
  have `? a b c. s_tot = (a,b,c)`; e(tac[tcases]);
  e(elims);
  e(ssimp[dec_high_def,len_def,wf_substring_def]);
  have `! b c. (~(c<=b) /\ b <= c  ==> b <= c-1) /\ (c <= b ==> c <= 1+b)`; e(numLib.ARITH_TAC);
  e(ssimp[] THEN NO_TAC);
 *)
 e(tac[]);

 e(ssimp[update_lctxt_def]);
 e(tac[]);
val MEM_check_and_upd_lctxt_p_MEM_p = top_thm();

g `
MEM (pt,s_rem) (check_and_upd_lctxt t' (or_list (MAP (then_list2 t) xs)) i) ==> (root pt = NT t)
`;
e(intros);
have `? lc s_tot. i = <| lc1:=lc; sb1:=s_tot |>`; e(tac[icases_thm]);
e(elims);
have `? lc' s_rem' s_tot'. MEM (pt,s_rem') ((or_list (MAP (then_list2 t) xs)) <|lc1 := lc'; sb1 := s_tot'|>)`; 
 e(tac[MEM_check_and_upd_lctxt_p_MEM_p]);
e(Q_THIN_TAC `MEM _ _`);
e(elims);
e(ssimp[SYM(SPEC_ALL or_list_thm)]);
e(ssimp[listTheory.MEM_MAP]);  
e(ssimp[]);
e(ssimp[then_list_two_def]);
e(ssimp[myrr_def]);
e(ssimp[listTheory.MEM_MAP]);
e(Cases_on `y'` THEN ssimp[]);
e(ssimp[root_def] THEN NO_TAC);
val MEM_or_list_then_list2 = top_thm();

(*  + substrings and parse trees and subtrees and proper_subtrees *)

(*
g `
(substring_of pt = SOME x)
==> wf_substring x
`;
e(intros);
e(Cases_on `pt`);
 e(ssimp[substring_of_def_2]);
 e(Cases_on `p`);
 e(ssimp[LET_THM]);
 e(Cases_on `EVERY IS_SOME (MAP (\a. substring_of a) r)`);
  e(ssimp[]);
  e(tac[concatenate_list_SOME]);

  e(ssimp[] THEN NO_TAC);

 e(ssimp[substring_of_def_2]);
 e(Cases_on `p`);
 e(ssimp[]);
 e(tac[]);
val wf_substring_substring_of = top_thm();
*)

g `
! s_pt.
(substring_of (NODE(nt,pts)) = SOME s_pt)
==> MEM pt' pts
==> (substring_of pt' = SOME s_pt')
==> low s_pt <= low s_pt' /\ high s_pt' <= high s_pt /\ (string s_pt = string s_pt')
`;
e(Induct_on `pts`);
 e(ssimp[] THEN NO_TAC);

 e(intros);
 e(ssimp[]);
 dl();
  e(ssimp[]);
  e(ssimp[substring_of_def_2,LET_THM]);
  e(Cases_on `EVERY IS_SOME (MAP (\a. substring_of a) pts)`);
   e(ssimp[]);
   e(ssimp[concatenate_list_def_2]);
   e(Cases_on `MAP THE (MAP (\a. substring_of a) pts)`); 
    e(ssimp[]);
    e(numLib.ARITH_TAC);
   e(ssimp[]);
   e(Cases_on `concatenate_list (h'::t)`); e(ssimp[] THEN NO_TAC);
   e(ssimp[]);
   e(tac[concatenate_two_SOME,le_thms]);

   e(ssimp[] THEN NO_TAC);

  e(ssimp[]);
  have `? s_pts. substring_of (NODE(nt,pts)) = SOME s_pts`;
   e(ssimp[substring_of_def_2,LET_THM]);
   e(Cases_on `IS_SOME (substring_of h) /\ EVERY IS_SOME (MAP (\a. substring_of a) pts)`);
    e(ssimp[concatenate_list_def_2]);
    e(Cases_on `MAP THE (MAP (\a. substring_of a) pts)`);
     e(ssimp[] THEN NO_TAC);

     e(ssimp[]);
     e(Cases_on `concatenate_list (h'::t)`);
      e(ssimp[] THEN NO_TAC);

      e(ssimp[] THEN NO_TAC);
    e(ssimp[] THEN NO_TAC);
  e(elims);
  xal `s_pts`;
  e(ssimp[]);
  e(ssimp[substring_of_def_2,LET_THM]);
  e(Cases_on `EVERY IS_SOME (MAP (\a. substring_of a) pts)`);
   e(ssimp[]);
   e(Cases_on `IS_SOME (substring_of h)` THEN ssimp[]);
   e(ssimp[concatenate_list_def_2]);
   e(Cases_on `MAP THE (MAP (\a. substring_of a) pts)` THEN ssimp[]);
   have `high s_pt = high s_pts`; e(tac[concatenate_two_SOME]);
   have `low s_pt <= low s_pts`; e(tac[concatenate_two_SOME]);
   e(tac[concatenate_two_SOME,le_thms]);

   e(ssimp[] THEN NO_TAC);
val low_s_pt_low_s_pt'_high_s_pt_high_s_pt' = top_thm();

g `
MEM x (subtrees y) = (x=y) \/ MEM x (proper_subtrees y)
`;
e(ssimp[proper_subtrees_def]);
e(Cases_on `subtrees y` THEN ssimp[]);
 e(Cases_on `y` THEN ssimp[]);
  e(Cases_on `p` THEN ssimp[subtrees_def_2]);
  
  e(Cases_on `p` THEN ssimp[subtrees_def_2]);

 e(Cases_on `y` THEN ssimp[]);
  e(Cases_on `p` THEN ssimp[subtrees_def_2]);
  
  e(Cases_on `p` THEN ssimp[subtrees_def_2]);
val MEM_subtrees_MEM_proper_subtrees = top_thm(); 


g `
! pt. ! pt'.
MEM pt' (proper_subtrees pt) ==> parse_tree_size pt' < parse_tree_size pt
`;
want `! n. ! pt. ! pt'.
(parse_tree_size pt = n)
==> MEM pt' (proper_subtrees pt) ==> parse_tree_size pt' < parse_tree_size pt
`; e(tac[]);
e(completeInduct_on `n`);
e(intros);
e(Cases_on `pt` THEN ssimp[]);
 (* NODE *)
 e(Cases_on `p`);
 e(RENAME_TAC [``q:nonterm``|->``nt:nonterm``,``r:parse_tree list``|->``pts:parse_tree list``]);
 e(REORDER_TAC `MEM pt' (proper_subtrees (NODE (nt,pts)))`);
 e(assimp[proper_subtrees_def]0);
 e(ssimp[subtrees_def_2]);
 e(ssimp[listTheory.MEM_FLAT]);
 e(RENAME_TAC [``l:parse_tree list``|->``pt2:parse_tree list``]);
 e(ssimp[listTheory.MEM_MAP]);
 e(RENAME_TAC [``a:parse_tree``|->``pt3:parse_tree``]);
 e(ssimp[]);
 have `MEM pt3 pts /\ MEM pt' (subtrees pt3) /\ (parse_tree_size (NODE(nt,pts)) = n)`; e(tac[]);
 want `parse_tree_size pt' < n`; e(tac[]);
 have `parse_tree_size pt3 < n`; e(tac[MEM_pt_pts_parse_tree_size]); 
 xal `parse_tree_size pt3`;
 il 0; e(INIT_TAC);
 xal `pt3`;
 xal `pt'`;
 il 0; e(tac[]);
 e(ssimp[MEM_subtrees_MEM_proper_subtrees]);
 e(tac[less_le,le_thms]); 

 (* LF *)
 e(ssimp[proper_subtrees_def,subtrees_def_2]); 
 e(Cases_on `p` THEN ssimp[]);
val MEM_proper_subtrees_parse_tree_size = top_thm();


(*  + hereditary lemmas *)


(* FIXME substring_of clause is slightly odd; note this is downwards, ie if we know something about NODE(nt,pts) we know something about pt IN pts *)
g `
(MEM pt pts
  ==> 
  (wf_prs_tree (NODE(nt,pts)) ==> wf_prs_tree pt)  
  /\ (wf_parse_tree (NODE(nt,pts)) ==> wf_parse_tree pt)
  /\ (NODE(nt,pts) IN pts_of ss g ==> pt IN pts_of ss g)
  /\ (good_tree (NODE(nt,pts)) ==> good_tree pt)
  /\ (admits lc (NODE(nt,pts)) ==> admits ((nt,THE(substring_of (NODE(nt,pts))))::lc) pt))
/\
(IS_SOME (substring_of (NODE(nt,pts))) ==> EVERY IS_SOME (MAP (\a. substring_of a) pts))
/\ (((substring_of (NODE(nt,pts)) = SOME s_pt) ==> EVERY IS_SOME (MAP (\a. substring_of a) pts)))
`;
have `! s_pt. ((substring_of (NODE(nt,pts)) = SOME s_pt) ==> EVERY IS_SOME (MAP (\a. substring_of a) pts))`;
 e(intros);
 e(ssimp[substring_of_def_2,LET_THM]);
 e(Cases_on `EVERY IS_SOME (MAP (\a. substring_of a) pts)`);
  e(ssimp[] THEN NO_TAC);

  e(ssimp[] THEN NO_TAC);
cr(); defer();
 e(ssimp[]);
 e(Cases_on `substring_of (NODE (nt,pts))` THEN ssimp[] THEN NO_TAC);
e(intros);
have `! x. MEM x (subtrees pt) ==> MEM x (subtrees (NODE(nt,pts)))`;
 e(intros);
 e(ssimp[subtrees_def_2]);
 dr2();
 e(ssimp[listTheory.MEM_FLAT]);
 e(ssimp[listTheory.MEM_MAP]);
 e(tac[]);
have `wf_prs_tree (NODE(nt,pts)) ==> wf_prs_tree pt`;
 e(ssimp[wf_prs_tree_def_2]);
 e(ssimp[listTheory.EVERY_MEM] THEN NO_TAC);
have `(wf_parse_tree (NODE(nt,pts)) ==> wf_parse_tree pt)`;
 e(intros);
 e(ssimp[wf_parse_tree_def_2,wf_prs_tree_def_2]);
 e(ssimp[wf_parse_tree_def]);
 e(ssimp[listTheory.EVERY_MEM]);
 e(ssimp[substring_of_def_2,LET_THM]);
 e(Cases_on `EVERY IS_SOME (MAP (\a. substring_of a) pts)`);
  e(ssimp[]);
  e(ssimp[listTheory.EVERY_MEM]);
  e(ssimp[listTheory.MEM_MAP]);
  xal `substring_of pt`;
  il 0; e(tac[]);
  e(ssimp[]);
  ir();
  e(ssimp[] THEN NO_TAC);

  e(ssimp[] THEN NO_TAC);
have `good_tree (NODE (nt,pts)) ==> good_tree pt`;
 e(intros);
 e(ssimp[good_tree_def_2]);
 e(ssimp[good_tree_def]);
 e(ssimp[listTheory.EVERY_MEM] THEN NO_TAC);
e(ssimp[]);
e(cintros);
 (* pt IN pts_of ss g *)
 e(ssimp[pts_of_def,SPECIFICATION] THEN NO_TAC);

 (* admits *)
 e(elims);
 e(ssimp[]);
 e(ssimp[admits_def_2,LET_THM]);
 e(ssimp[listTheory.EVERY_MEM] THEN NO_TAC);
val hereditary_lemmas = top_thm();

g `
(! nt pts. P (NODE(nt,pts)) ==> ! pt'. MEM pt' pts ==> P pt')
==> ! pt. P pt ==> MEM pt' (proper_subtrees pt) ==> P pt'
`;
ir();
want `! n. ! pt. (parse_tree_size pt = n) /\ P pt /\ MEM pt' (proper_subtrees pt) ==> P pt'`; e(tac[]);
e(completeInduct_on `n`);
e(intros);
e(elims);
have `parse_tree_size pt' < n`; e(tac[MEM_proper_subtrees_parse_tree_size]);
e(Cases_on `pt` THEN ssimp[]);
 e(Cases_on `p` THEN ssimp[]);
 e(RENAME_TAC [``q:nonterm``|->``nt:nonterm``,``r:parse_tree list``|->``pts:parse_tree list``]);
 e(REORDER_TAC `MEM pt' (proper_subtrees (NODE (nt,pts)))`);
 e(assimp[proper_subtrees_def,subtrees_def_2]0);
 e(ssimp[listTheory.MEM_FLAT,listTheory.MEM_MAP]);
 e(RENAME_TAC [``l:parse_tree list``|->``pt2:parse_tree list``]);
 e(RENAME_TAC [``a:parse_tree``|->``pt3:parse_tree``]);
 e(ssimp[]);
 have `P pt3`; e(tac[MEM_pt_pts_parse_tree_size]);
 e(tac[MEM_subtrees_MEM_proper_subtrees,MEM_pt_pts_parse_tree_size]);

 e(ssimp[proper_subtrees_def,subtrees_def_2]);
 e(Cases_on `p` THEN ssimp[]);
val hereditary_proper_subtrees = top_thm();


g `
wf_prs_tree pt /\ MEM pt' (proper_subtrees pt) ==> wf_prs_tree pt'
`;
e(ASSUME_TAC (INST [``P:parse_tree->bool``|->``\ pt. wf_prs_tree pt``] hereditary_proper_subtrees));
e(ssimp[]);
e(tac[hereditary_lemmas]);
val wf_prs_tree_proper_subtrees = top_thm();

g `
wf_parse_tree pt /\ MEM pt' (proper_subtrees pt) ==> wf_parse_tree pt'
`;
e(ASSUME_TAC (INST [``P:parse_tree->bool``|->``\ pt. wf_parse_tree pt``] hereditary_proper_subtrees));
e(ssimp[]);
e(tac[hereditary_lemmas]);
val wf_parse_tree_proper_subtrees = top_thm();

g `
good_tree pt /\ MEM pt' (proper_subtrees pt) ==> good_tree pt'
`;
e(ASSUME_TAC (INST [``P:parse_tree->bool``|->``\ pt. good_tree pt``] hereditary_proper_subtrees));
e(ssimp[]);
e(tac[hereditary_lemmas]);
val good_tree_proper_subtrees = top_thm();

g `
pt IN pts_of ss g /\ MEM pt' (proper_subtrees pt) ==> pt' IN pts_of ss g
`;
e(ASSUME_TAC (INST [``P:parse_tree->bool``|->``\ pt. pt IN pts_of ss g``] hereditary_proper_subtrees));
e(ssimp[]);
e(tac[hereditary_lemmas]);
val pts_of_proper_subtrees = top_thm();





(*  + basic facts about grammar_to_parser *)

g `
wf_p_of_tm p_of_tm /\ wf_grammar g
==> (grammar_to_parser p_of_tm g sym = p) 
==> MEM (pt,s_rem) (p <| lc1:=lc; sb1:=s_tot |>) 
==> (root pt = sym)
`;
e(intros);
e(Cases_on `sym`);
 e(SYM_TAC `_=p`);
 e(ssimp[grammar_to_parser_def_2]);
 e(ssimp[myrr_def]);
 e(ssimp[listTheory.MEM_MAP]);
 e(Cases_on `y` THEN ssimp[]);
 e(ssimp[root_def] THEN NO_TAC);

 e(SYM_TAC `_=p`);
 e(ssimp[grammar_to_parser_def_2]);
 e(ssimp[LET_THM]);
 e(tac[MEM_or_list_then_list2]);
val root_grammar_to_parser_sym = top_thm();    

g `
wf_p_of_tm p_of_tm /\ wf_grammar g
==> ! pts s_rem lc s_tot.
MEM (pts,s_rem) (then_list (MAP (\sym'. grammar_to_parser p_of_tm g sym') alt) <|lc1 := lc; sb1 := s_tot|>) ==>
(MAP root pts = alt)
`;
e(Induct_on `alt`);
 e(ssimp[then_list_def_2,always_def] THEN NO_TAC);

 e(intros);
 e(RENAME_TAC [``h:symbol``|->``sym:symbol``]);
 e(ssimp[]);
 e(ssimp[then_list_def_2,myrr_def]);
 e(ssimp[mythen_def,LET_THM]);
 e(ssimp[listTheory.MEM_MAP]);
 e(SYM_TAC `(pts,s_rem) = _`);
 e(Cases_on `y` THEN ssimp[]);
 e(Cases_on `q` THEN ssimp[]);
 e(Cases_on `pts` THEN ssimp[]);
 e(REMOVE_VARS_TAC [`r`,`q'`,`r'`]);
 e(RENAME_TAC [``h:parse_tree``|->``pt:parse_tree``,``t:parse_tree list``|->``pts:parse_tree list``]);
 e(ssimp[listTheory.MEM_FLAT]);
 e(ssimp[listTheory.MEM_MAP]);
 e(Cases_on `y` THEN ssimp[]);
 e(REMOVE_VAR_TAC `l`);
 have `root q = sym`; e(tac[root_grammar_to_parser_sym]);
 cr();
  e(ssimp[listTheory.MEM_MAP]);
  e(Cases_on `y` THEN ssimp[] THEN NO_TAC);
 
  e(ssimp[listTheory.MEM_MAP]);
  e(Cases_on `y` THEN ssimp[]);
  e(tac[]);
val MEM_then_list_MAP_root = top_thm();

(*  + prefix_sound_grammar_to_parser_thm *)


g `
wf_p_of_tm p_of_tm /\ wf_grammar g
==> (grammar_to_parser p_of_tm g = p) 
==> ((\ pt. ? lc s_tot sym s_rem. MEM (pt,s_rem) (p sym <| lc1:=lc; sb1:=s_tot |>)) = P)
==> (P (NODE(nt,pts)) ==> ! pt'. MEM pt' pts ==> P pt')
`;
e(intros);
e(SYM_TAC `_=P`);
e(REORDER_TAC `P _`);
e(assimp[]0);
e(SYM_TAC `P=_`);
e(elims);
e(SYM_TAC `_=p`);
e(ssimp[]);
have `sym = root (NODE(nt,pts))`; e(tac[root_grammar_to_parser_sym]);
e(ssimp[root_def]);
e(REORDER_TAC `MEM (NODE(nt,pts),s_rem) _`);
e(assimp[grammar_to_parser_def_2]0);
e(ssimp[LET_THM]);
have `?lc' s_rem' s_tot'. MEM (NODE(nt,pts),s_rem') 
           (or_list
              (MAP (then_list2 nt)
                 (MAP (MAP (\ sym'. grammar_to_parser p_of_tm g sym'))
                    (FLAT (MAP SND (FILTER (\ (nt',rhs). nt' = nt) g)))))  <|lc1 := lc'; sb1 := s_tot'|>)
`; e(tac[MEM_check_and_upd_lctxt_p_MEM_p]);
e(Q_THIN_TAC `MEM (NODE(nt,pts),s_rem) _`);
e(elims);
e(ssimp[SYM (SPEC_ALL or_list_thm)]);
e(ssimp[listTheory.MEM_MAP]);
e(RENAME_TAC [``y':symbol list``|->``alt:symbol list``]);
e(ssimp[]);
e(REMOVE_VARS_TAC [`y`,`p`,`sym`,`p'`]);
e(ssimp[listTheory.MEM_FLAT]);
e(RENAME_TAC [``l:symbol list list``|->``alts:symbol list list``]);
e(ssimp[then_list_two_def,myrr_def]);
e(ssimp[listTheory.MEM_MAP]);
e(SYM_TAC `alts=_`);
e(ssimp[]);
e(Cases_on `y` THEN ssimp[]);
e(RENAME_TAC [``q:nonterm``|->``nt':nonterm``]);
e(REMOVE_VAR_TAC `r`);
e(ssimp[listTheory.MEM_FILTER]);
e(Cases_on `y'` THEN ssimp[]);
e(SYM_TAC `pts = q`);
e(SYM_TAC `s_rem' = r`);
e(ssimp[]);
e(REMOVE_VARS_TAC [`q`,`r`,`nt'`]);
want `! pts. ! pt'. ! lc' s_tot' s_rem'. MEM pt' pts ==> MEM (pts,s_rem') (then_list (MAP (\sym'. grammar_to_parser p_of_tm g sym') alt) <|lc1 := lc'; sb1:= s_tot'|>) ==> P pt'`; e(tac[]);
e(Q_THIN_TAC `MEM pt' pts`);
e(Q_THIN_TAC `MEM (pts,s_rem') _`);
e(Q_THIN_TAC `MEM _ _`);
e(Q_THIN_TAC `MEM _ _`);
e(Induct_on `alt`);
 e(ssimp[then_list_def_2,always_def] THEN NO_TAC);

 val here_1497 = p(); dropn 1; add(here_1497);
 e(intros);
 e(RENAME_TAC [``h:symbol``|->``sym:symbol``]);
 have `LENGTH pts = LENGTH (MAP (\sym'. grammar_to_parser p_of_tm g sym') (sym::alt))`; e(tac[LENGTH_pts_LENGTH_ps]);
 e(ssimp[]);
 e(Cases_on `pts` THEN ssimp[]);
 e(RENAME_TAC [``h:parse_tree``|->``pt:parse_tree``,``t:parse_tree list``|->``pts:parse_tree list``]);
 dl();
  (* pt' = pt *)
  e(REORDER_TAC `MEM _ _`);
  have `? s_rem''. MEM (pt,s_rem'') ((\ a. grammar_to_parser p_of_tm g sym a) <| lc1:=lc';sb1:=s_tot' |>)`; e(tac[MEM_cons_then_list]);
  e(Q_THIN_TAC `MEM _ _`);
  e(elims);
  e(SYM_TAC `_ = P`);
  e(ssimp[]);
  e(tac[]);

  e(tac[MEM_cons_then_list]);
val MEM_NODE_grammar_to_parser_MEM_child_grammar_to_parser = top_thm();


g `
wf_p_of_tm p_of_tm /\ wf_grammar g
==> (grammar_to_parser p_of_tm g = p) 
==> ((\ pt. ? lc s_tot sym s_rem. MEM (pt,s_rem) (p sym <| lc1:=lc; sb1:=s_tot |>)) = P)
==> P pt ==> ! pt'. MEM pt' (proper_subtrees pt) ==> P pt'
`;
e(tac[MEM_NODE_grammar_to_parser_MEM_child_grammar_to_parser,hereditary_proper_subtrees]);
val MEM_grammar_to_parser_MEM_proper_subtrees_grammar_to_parser = top_thm();

(* uses previous MEM_then_list_MAP_root *)

g `
wf_p_of_tm p_of_tm /\ wf_grammar g
==> (grammar_to_parser p_of_tm g = p) 
==> MEM (NODE(nt,pts),s_rem) (p sym <| lc1:=lc; sb1:=s_tot |>) 
==> EXISTS (\ (nt',alts). (nt' = nt) /\ MEM (MAP root pts) alts) g
`;
e(intros);
have `sym = NT nt`;
 have `root (NODE(nt,pts)) = sym`; e(tac[root_grammar_to_parser_sym]);
 e(ssimp[root_def] THEN NO_TAC);
e(ssimp[]);
e(SYM_TAC `_ = p`);
e(ssimp[]);
e(ssimp[grammar_to_parser_def_2]);
e(ssimp[LET_THM]);
have `? lc' s_rem' s_tot'. MEM (NODE(nt,pts),s_rem') ((or_list
            (MAP (then_list2 nt)
               (MAP (MAP (\ sym'. grammar_to_parser p_of_tm g sym'))
                  (FLAT (MAP SND (FILTER (\ (nt',rhs). nt' = nt) g)))))) <|lc1 := lc'; sb1 := s_tot'|>)
`;
 e(tac[MEM_check_and_upd_lctxt_p_MEM_p]);
e(elims);
e(Q_THIN_TAC `MEM (NODE (nt,pts),s_rem) _`);
e(ssimp[SYM (SPEC_ALL or_list_thm)]);
e(ssimp[listTheory.MEM_MAP]);
e(RENAME_TAC [``y':symbol list``|->``alt:symbol list``]);
e(ssimp[]);
e(REMOVE_VARS_TAC [`y`,`p`,`sym`,`p'`]);
e(ssimp[listTheory.MEM_FLAT]);
e(RENAME_TAC [``l:symbol list list``|->``alts:symbol list list``]);
e(ssimp[listTheory.EXISTS_MEM]);
er `(nt,alts)`;
e(ssimp[]);
cr();
 want `MEM (nt,alts) g`; e(INIT_TAC);
 e(ssimp[listTheory.MEM_MAP]);
 e(ssimp[listTheory.MEM_FILTER]);
 e(Cases_on `y` THEN ssimp[] THEN NO_TAC);

 want `MEM (MAP root pts) alts`; e(INIT_TAC);
 want `MAP root pts = alt`; e(tac[]);
 e(Q_THIN_TAC `MEM alts _`);
 e(Q_THIN_TAC `MEM alt alts`);
 e(ssimp[then_list_two_def]);
 e(ssimp[myrr_def]);
 e(ssimp[listTheory.MEM_MAP]);
 e(Cases_on `y` THEN ssimp[]);
 e(SYM_TAC `_=q`);
 e(SYM_TAC `_=r`);
 e(ssimp[]);
 e(REMOVE_VARS_TAC [`q`,`r`]);
 e(tac[MEM_then_list_MAP_root]);
val EXISTS_MEM_MAP_root_pts_alts_g = top_thm();


(* FIXME can we simplify the following with MEM_check_and_upd_lctxt_p_MEM_p etc? *)


g `
wf_grammar g /\ wf_p_of_tm p_of_tm /\ (grammar_to_parser p_of_tm g = p) 
==> MEM (pt,s_rem) (p sym <| lc1:=lc; sb1:=s_tot |>) 
==> wf_prs_tree pt
`;
(* induction on pt, have that pts cannot be [] otherwise rhs of rule was empty? *)
ir();
val tm = ``! s_rem. ! sym:symbol. ! lc. ! s_tot.
MEM (pt,s_rem) ((p:symbol -> parse_tree parser) sym <| lc1:=lc; sb1:=s_tot |>) 
==> wf_prs_tree pt
``;
want `! n. ! pt. (parse_tree_size pt = n) ==> ^tm`;
 e(tac[]);
e(completeInduct_on `n`);
e(intros);
have `root pt = sym`; e(tac[root_grammar_to_parser_sym]);
e(Cases_on `sym`);
 e(ssimp[]);
 e(Cases_on `pt` THEN Cases_on `p'` THEN ssimp[root_def]);
 e(ssimp[wf_prs_tree_def_2] THEN NO_TAC);
 (* e(SYM_TAC `_=p`); 
 e(ssimp[]);
 e(ssimp[grammar_to_parser_def_2]);
 e(ssimp[myrr_def]);
 e(ssimp[listTheory.MEM_MAP]);
 e(Cases_on `y` THEN ssimp[]);
 e(ssimp[wf_p_of_tm_def]);
 xal `t`;
 e(ssimp[LET_THM]);
 have `concatenate_two q' r' = SOME s_tot`; e(tac[]);
 e(tac[concatenate_two_SOME]);
 *)

 val here_1200 = p(); dropn 1; add(here_1200);
 e(Cases_on `pt` THEN Cases_on `p'` THEN ssimp[root_def]);
 e(ssimp[wf_prs_tree_def_2]);
 e(RENAME_TAC [``t:nonterm``|->``nt:nonterm``, ``r:parse_tree list``|->``pts:parse_tree list``]);
 cr();
  (* pts <> [] *)
  ir();
  have `EXISTS (\ (nt',alts). (nt' = nt) /\ MEM (MAP root pts) alts) g`; e(tac[EXISTS_MEM_MAP_root_pts_alts_g]);
  e(ssimp[]);
  e(ssimp[listTheory.EXISTS_MEM]);
  e(ssimp[wf_grammar_def]);
  e(Cases_on `e` THEN ssimp[]);
  have `MEM r (MAP SND g)`;
   e(ssimp[listTheory.MEM_MAP]);
   er `(nt,r)`;
   e(ssimp[] THEN NO_TAC);
  e(tac[]);

  (* EVERY *)
  e(ssimp[listTheory.EVERY_MEM]);  
  e(intros);
  e(RENAME_TAC [``a:parse_tree``|->``pt:parse_tree``]);    
  xal `parse_tree_size pt`;
  il 0; e(tac[MEM_pt_pts_parse_tree_size]);
  xal `pt`;
  il 0; e(tac[]);
  e(ASSUME_TAC (GEN ``P:parse_tree -> bool`` MEM_NODE_grammar_to_parser_MEM_child_grammar_to_parser));
  xal `(\pt. ?lc s_tot sym s_rem. MEM (pt,s_rem) (p sym <|lc1 := lc; sb1 := s_tot|>))`;
  e(ssimp[]);
  e(tac[]);
val MEM_grammar_to_parser_wf_prs_tree = top_thm();


(* do the substring lemmas first *)

g `
! ps.
(pts <> []) (* if pts = [] then our lemma doesn't hold *)
==> (! p lc s_tot pt s_rem. ? s_pt. MEM p ps /\ MEM pt pts /\ MEM (pt,s_rem) (p <| lc1:=lc; sb1:=s_tot |>) ==> (substring_of pt = SOME s_pt) /\ (concatenate_two s_pt s_rem = SOME s_tot))
==> ! lc s_tot s_rem. MEM (pts,s_rem) (then_list ps <| lc1:=lc; sb1:=s_tot |>)
==> ? s_pts. (substring_of (NODE(nt,pts)) = SOME s_pts) /\ (concatenate_two s_pts s_rem = SOME s_tot)
`;
e(Induct_on `pts`);
 e(ssimp[] THEN NO_TAC);

 e(intros);
 e(elims);
 e(CONV_TAC (MINISCOPE_EXISTS_CONV true));
 e(intros);
 e(RENAME_TAC [``h:parse_tree``|->``pt:parse_tree``]);
 e(ssimp[]);
 e(Cases_on `pts=[]`);
  e(ssimp[]);
  have `LENGTH [pt] = LENGTH ps`; e(tac[LENGTH_pts_LENGTH_ps]);
  e(ssimp[]);
  e(Cases_on `ps`);
   e(ssimp[then_list_def_2,always_def] THEN NO_TAC);

   e(RENAME_TAC [``h:parse_tree parser``|->``p:parse_tree parser``,``t:parse_tree parser list``|->``ps:parse_tree parser list``]);
   e(ssimp[]);  
   xal `p`;
   xal `lc`;
   xal `s_tot`;
   xal `pt`;
   xal `s_rem`;
   e(elims);
   e(ssimp[]);
   e(Cases_on `ps` THEN ssimp[]);
   e(ssimp[then_list_def_2]);
   e(ssimp[mythen_def,myrr_def]);
   e(ssimp[LET_THM]);
   e(ssimp[listTheory.MEM_MAP]);
   e(ssimp[listTheory.MEM_FLAT]);
   e(ssimp[listTheory.MEM_MAP]);
   e(Cases_on `y` THEN ssimp[]);
   e(Cases_on `y'` THEN ssimp[]);
   e(Cases_on `q` THEN ssimp[]);
   e(SYM_TAC `[] = r''` THEN ssimp[]);
   e(ssimp[substring_of_def_2,LET_THM]);
   e(ssimp[always_def,substr_def]);
   e(ssimp[concatenate_list_def_2] THEN NO_TAC);   

  (* pts <> [] *)
  val here_1728 = p(); dropn 1; add(here_1728);
  e(ssimp[]);
  have `LENGTH (pt::pts) = LENGTH ps`; e(tac[LENGTH_pts_LENGTH_ps]);
  e(Cases_on `ps` THEN ssimp[]);
  e(RENAME_TAC [``h:parse_tree parser``|->``p:parse_tree parser``,``t:parse_tree parser list``|->``ps:parse_tree parser list``]);
  e(ssimp[]);  
  have `? s_rem'. MEM (pt,s_rem') (p <|lc1 := lc; sb1 := s_tot|>) /\ MEM (pts,s_rem) (then_list ps <|lc1 := lc; sb1 := s_rem'|>)`; 
   e(tac[MEM_cons_then_list]);
  e(elims);
  al `p`;
  xal `lc`;
  xal `s_tot`;
  xal `pt`;
  xal `s_rem'`;
  e(elims);
  e(ssimp[]);
  e(REORDER_TAC `! ps'. _ ==> _`);
  xal `ps`;
  il 0; e(tac[]);
  xal `lc`;   
  xal `s_rem'`;
  xal `s_rem`;
  e(elims);
  e(ssimp[]);
  have `? s_pt'. concatenate_two s_pt s_pts = SOME s_pt'`;
   e(ssimp[concatenate_two_def]);
   e(MY_ASSUME_TAC(INST [``s:substring``|->``s_rem':substring``] tcases_2));
   e(elims);
   e(MY_ASSUME_TAC(INST [``s:substring``|->``s_rem:substring``] tcases_2));
   e(elims);
   e(MY_ASSUME_TAC(INST [``s:substring``|->``s_pts:substring``] tcases_2));
   e(elims);
   e(MY_ASSUME_TAC(INST [``s:substring``|->``s_tot:substring``] tcases_2));
   e(elims);
   e(MY_ASSUME_TAC(INST [``s:substring``|->``s_pt:substring``] tcases_2));
   e(elims);
   e(ssimp[string_def,low_def,high_def,LET_THM]);
   e(ssimp ty_substring_simps);
   have `wf_substring (a,b'''',c)`; e(tac[wf_substring_thms]);
   e(ssimp ty_substring_simps);
   have `wf_substring (a',b'',c')`; e(tac[wf_substring_thms]);
   e(ssimp ty_substring_simps THEN NO_TAC);
  e(elims);
  er `s_pt'`;
  want `(substring_of (NODE (nt,pt::pts)) = SOME s_pt') /\ (concatenate_two s_pt' s_rem = SOME s_tot)`; e(INIT_TAC);
  cr();
   e(ssimp[substring_of_def_2,LET_THM]);
   e(Cases_on `EVERY IS_SOME (MAP (\a. substring_of a) pts)` THEN ssimp[]);
   e(ssimp[concatenate_list_def_2]);
   e(Cases_on `MAP THE (MAP (\a. substring_of a) pts)` THEN ssimp[] THEN NO_TAC);

   e(ssimp[concatenate_two_def]);
   e(MY_ASSUME_TAC(INST [``s:substring``|->``s_rem':substring``] tcases_2));
   e(elims);
   e(MY_ASSUME_TAC(INST [``s:substring``|->``s_rem:substring``] tcases_2));
   e(elims);
   e(MY_ASSUME_TAC(INST [``s:substring``|->``s_pts:substring``] tcases_2));
   e(elims);
   e(MY_ASSUME_TAC(INST [``s:substring``|->``s_tot:substring``] tcases_2));
   e(elims);
   e(MY_ASSUME_TAC(INST [``s:substring``|->``s_pt:substring``] tcases_2));
   e(elims);
   e(MY_ASSUME_TAC(INST [``s:substring``|->``s_pt':substring``] tcases_2));
   e(elims);
   e(ssimp[]);
   e(ssimp[string_def,low_def,high_def,LET_THM]);
   e(ssimp ty_substring_simps);
   have `wf_substring (a',b'''',b') /\ wf_substring (a',b'''',c) /\ wf_substring (a',b'',c') /\ wf_substring (a',b'',c)`; e(tac[wf_substring_thms]);
   e(ssimp ty_substring_simps THEN NO_TAC);
val prefix_sound_substring_then_list = top_thm();

(* depends on previous lemma prefix_sound_substring_then_list *)

g `
prefix_sound_grammar_to_parser_thm
`;
e(ssimp[prefix_sound_grammar_to_parser_thm_def]);
e(intros);
e(MY_LET_INTRO_TAC);
e(ssimp[prefix_sound_def]);
ir();
val tm = ``
! sym. ! s_tot. ! lc. ! s_rem. ? s_pt. 
  let p = grammar_to_parser p_of_tm g sym in
  let ss_of_tm = ss_of_tm_of p_of_tm in
  MEM (pt,s_rem) (p <| lc1 := lc; sb1 := s_tot |>)
  ==>
  pt IN pts_of ss_of_tm g /\ (root pt = sym) /\ (substring_of pt = SOME s_pt) /\ (concatenate_two s_pt s_rem = SOME s_tot)
``;
want `! pt. ^tm`;
 e(ssimp[toinput_def]);
 e(ssimp[LET_THM]);
 e(tac[]);
e(Q_THIN_TAC `grammar_to_parser p_of_tm g sym = p`);
want `! n. !pt. (parse_tree_size pt = n) ==> ^tm`; e(tac[]);
e(completeInduct_on `n`);
e(intros);
have `? p. grammar_to_parser p_of_tm g sym = p`; e(tac[]);
e(elims);
have `? ss_of_tm. ss_of_tm_of p_of_tm = ss_of_tm`; e(tac[]);
e(elims);
e(SIMP_TAC (srw_ss()) [LET_THM]);
e(CONV_TAC (MINISCOPE_EXISTS_CONV true));
e(intros);
e(Cases_on `pt`);
 e(Cases_on `p'`);
 e(RENAME_TAC [``q:nonterm``|->``nt:nonterm``,``r:parse_tree list``|->``pts:parse_tree list``]);
 have `(root (NODE (nt,pts)) = sym)`; e(tac[root_grammar_to_parser_sym]);
 e(ssimp[root_def_2]);
 e(SYM_TAC `_=sym`);
 have `? s_pts. (substring_of (NODE (nt,pts)) = SOME s_pts) /\ (concatenate_two s_pts s_rem = SOME s_tot)`; 
  have `EXISTS (\ (nt',alts). (nt'=nt) /\ MEM (MAP root pts) alts) g`;
   e(MATCH_MP_TAC' (INST [``p:symbol->parse_tree parser``|->``grammar_to_parser p_of_tm g``] EXISTS_MEM_MAP_root_pts_alts_g));
    e(tac[]);
  e(ssimp[listTheory.EXISTS_MEM]);
  e(Cases_on `e`);
  e(RENAME_TAC [``q:nonterm``|->``nt':nonterm``,``r:symbol list list``|->``alts:symbol list list``]);
  e(ssimp[]);
  have `? alt. MAP root pts = alt`; e(tac[]);
  e(elims); e(ssimp[]);
  val here_1831 = p(); dropn 1; add(here_1831);
  e(ASSUME_TAC prefix_sound_substring_then_list); (* FIXMEWF need wf_substring s_tot' in second assum *)
  xal `MAP (grammar_to_parser p_of_tm g) alt`;
  il 0; 
   ir();
   e(ssimp[wf_grammar_def]);
   xal `alts`;
   e(ssimp[]);
   e(ssimp[listTheory.MEM_MAP]);
   xal `(nt,alts)`;
   e(ssimp[] THEN NO_TAC);
  il 0; 
   e(intros);
   e(CONV_TAC (MINISCOPE_EXISTS_CONV true));
   e(intros);
   xal `parse_tree_size pt`;
   il 0; e(tac[MEM_pt_pts_parse_tree_size]);
   xal `pt`;
   il 0; e(tac[]);
   xal `root pt`;
   xal `s_tot'`;
   xal `lc'`;
   xal `s_rem'`;
   e(elims);
   e(ssimp[LET_THM]);
   e(REORDER_TAC `_ ==> _`);
   il 0; 
    e(ssimp[listTheory.MEM_MAP]);
    e(ssimp[]);
    e(tac[root_grammar_to_parser_sym]); (* FIXMEWF need wf_substring s_tot' *)
   e(tac[]);
  e(SYM_TAC `_=p`);
  e(REORDER_TAC `MEM (NODE (nt,pts),s_rem) (p <|lc1 := lc; sb1 := s_tot|>)`);
  e(ssimp[grammar_to_parser_def_2]);
  e(ssimp[LET_THM]);
  e(ssimp[check_and_upd_lctxt_def]);
  e(Cases_on `EXISTS ($= (nt,s_tot)) lc` THEN ssimp[]);
   e(Cases_on `len s_tot = 0` THEN ssimp[LET_THM]);
   e(ssimp[ignr_last_def]);
   e(ssimp[substr_def]);
   e(ssimp[LET_THM]);
   e(ssimp[listTheory.MEM_MAP]);
   e(Cases_on `y` THEN ssimp[]);
   e(ssimp[lift_def]);
   e(ssimp[update_lctxt_def]);
   (*
   have `wf_substring (dec_high 1 s_tot)`; 
    have `? a b c. s_tot = (a,b,c)`; e(tac[tcases]);
    e(elims);
    e(ssimp[wf_substring_def,dec_high_def,len_def]);
    have `! b c. (b <= c /\ ~ (c <= b) ==> b <= c - 1) /\ (c <= STRLEN a ==> c <= 1 + STRLEN a)`; e(numLib.ARITH_TAC);
    e(tac[]);
   *)
   xal `(nt,dec_high 1 s_tot)::lc`;
   xal `dec_high 1 s_tot`;
   xal `r`;
   il 0;
    e(SYM_TAC `_=q` THEN ssimp[]);
    e(ssimp[SYM(SPEC_ALL or_list_thm)]);
    e(ssimp[listTheory.MEM_MAP]);  
    e(ssimp[]);
    e(REORDER_TAC `MEM _ (then_list2 _ _ _)`);
    e(ssimp[then_list_two_def]);
    e(ssimp[myrr_def]);
    e(ssimp[listTheory.MEM_MAP]);
    e(Cases_on `y''` THEN ssimp[]);
    have `y' = MAP root q'`; e(tac[MEM_then_list_MAP_root]);
    e(ssimp[]);
    have `(\sym'. grammar_to_parser p_of_tm g sym') = grammar_to_parser p_of_tm g`; e(tac[]);
    e(ssimp[] THEN NO_TAC);
   e(elims);
   er `s_pts`;
   e(ssimp[]);
   have `concatenate_two s_pts (inc_high 1 r) = SOME s_tot`;
    val here_1895 = p(); dropn 1; add(here_1895);
    e(ssimp[concatenate_two_def]);
    e(MY_ASSUME_TAC(INST [``s:substring``|->``r:substring``] tcases_2));
    e(elims);
    e(MY_ASSUME_TAC(INST [``s:substring``|->``s_tot:substring``] tcases_2));
    e(elims);
    e(MY_ASSUME_TAC(INST [``s:substring``|->``s_pts:substring``] tcases_2));
    e(elims);
    e(ssimp[low_def,high_def,string_def,inc_high_def,dec_high_def,len_def,LET_THM]);
    e(ssimp ty_substring_simps);
    have `c' - b' <> 0 ==> (c' - 1 + 1 = c')`; e(numLib.ARITH_TAC);
    e(ssimp[]);
    have `wf_substring (a',b',c' - 1)`; e(tac[wf_substring_thms]);
    e(ssimp ty_substring_simps);
    have `wf_substring (a,b'',c)`; e(tac[wf_substring_thms]);
    e(ssimp ty_substring_simps);
    have `wf_substring (a',b,c')`; e(tac[wf_substring_thms]);
    e(ssimp ty_substring_simps THEN NO_TAC);
   e(INIT_TAC);

   (* ~ EXISTS *)
   val here_1925 = p(); dropn 1; add(here_1925);
   e(ssimp[LET_THM]);
   e(ssimp[update_lctxt_def]);
   xal `(nt,s_tot)::lc`;
   xal `s_tot`;
   xal `s_rem`;
   il 0;
    e(ssimp[SYM(SPEC_ALL or_list_thm)]);
    e(ssimp[listTheory.MEM_MAP]);  
    e(ssimp[]);
    e(REORDER_TAC `MEM _ (then_list2 _ _ _)`);
    e(ssimp[then_list_two_def]);
    e(ssimp[myrr_def]);
    e(ssimp[listTheory.MEM_MAP]);
    e(Cases_on `y''` THEN ssimp[]);
    have `y' = MAP root q`; e(tac[MEM_then_list_MAP_root]);
    e(ssimp[]);
    have `(\sym'. grammar_to_parser p_of_tm g sym') = grammar_to_parser p_of_tm g`; e(tac[]);
    e(ssimp[] THEN NO_TAC);
   e(tac[]);
 e(elims);
 er `s_pts`;
 e(ssimp[]);
 want `NODE (nt,pts) IN pts_of ss_of_tm g`; e(INIT_TAC);
 e(SIMP_TAC (srw_ss()) [pts_of_def,SPECIFICATION]);
 cr();
  (* wf_parse_tree pt *)
  val here_1147 = p(); dropn 1; add(here_1147);
  e(ssimp[wf_parse_tree_def]);
  e(tac[MEM_grammar_to_parser_wf_prs_tree]);

  e(intros);
  e(ssimp[MEM_subtrees_MEM_proper_subtrees]);
  dl();
   e(ssimp[]);
   e(tac[EXISTS_MEM_MAP_root_pts_alts_g]);

   (* MEM pt' (proper_subtrees (NODE (nt,pts))) *)
   have `? lc s_tot sym s_rem. MEM (pt',s_rem) (grammar_to_parser p_of_tm g sym <| lc1:=lc; sb1:=s_tot |>)`; 
    e(ASSUME_TAC (GENL [``pt:parse_tree``,``P:parse_tree -> bool``,``p:symbol -> parse_tree parser``] MEM_grammar_to_parser_MEM_proper_subtrees_grammar_to_parser));
    e(ssimp[]);
    xal `NODE(nt,pts)`;
    e(tac[]);
   e(elims);
   e(Cases_on `pt'`);
    e(Cases_on `p'`);
    e(ssimp[]);
    e(tac[EXISTS_MEM_MAP_root_pts_alts_g]);
 
    val here_1799 = p(); dropn 1; add(here_1799);
    e(Cases_on `p'`);
    e(ssimp[]);
    have `sym' = root (LF(q,r))`; e(tac[root_grammar_to_parser_sym]);
    e(ssimp[root_def]);
    e(ssimp[grammar_to_parser_def_2]);
    e(ssimp[myrr_def]);
    e(ssimp[listTheory.MEM_MAP]);
    e(Cases_on `y` THEN ssimp[]);
    e(SYM_TAC `_=ss_of_tm`);
    e(ssimp[ss_of_tm_of_def,LET_THM]);
    want `q' IN {s | ?i s'. MEM (s,s') (p_of_tm q i)}`;
     e(asimp[SPECIFICATION]0); e(INIT_TAC);
    e(ssimp[]);
    e(tac[]);
  
 (* LF *)
 val here_1816 = p(); dropn 1; add(here_1816);
 e(Cases_on `p'` THEN ssimp[]);
 have `sym = (root (LF(q,r)))`; e(tac[root_grammar_to_parser_sym]);
 e(ssimp[root_def]);
 er `r`; 
 e(ssimp[substring_of_def_2]);
 e(SYM_TAC `_=p`);
 e(ssimp[]);
 e(ssimp[grammar_to_parser_def_2,myrr_def]);
 e(ssimp[listTheory.MEM_MAP]);
 e(Cases_on `y` THEN ssimp[]);
 e(ssimp[wf_p_of_tm_def,LET_THM]);
 e(SIMP_TAC (srw_ss()) [SPECIFICATION]);
 e(ssimp[pts_of_def]);
 e(ssimp[subtrees_def_2]);
 e(SYM_TAC `_ = ss_of_tm`);
 e(ssimp[]);
 e(ssimp[ss_of_tm_of_def,LET_THM]);
 e(ssimp[wf_parse_tree_def,wf_prs_tree_def_2,substring_of_def_2]);
 e(tac[concatenate_two_SOME]);
val prefix_sound_grammar_to_parser_thm = top_thm();

(*  + prefix_sound_sound_thm *)

g `
prefix_sound_sound_thm
`;
e(ssimp[prefix_sound_sound_thm_def]);
e(intros);
e(ssimp[prefix_sound_def,sound_def]);
e(intros);
e(elims);
xal `s`;
xal `pt`;
e(elims);
e(ssimp[simple_parser_of_def]);
e(ssimp[listTheory.MEM_MAP]);
e(ssimp[listTheory.MEM_FILTER]);
e(Cases_on `y` THEN ssimp[]);
xal `r`;
e(elims);
e(ssimp[] THEN NO_TAC);
val prefix_sound_sound_thm = top_thm();

(*  + sound_grammar_to_parser_thm *)

g `
sound_grammar_to_parser_thm
`;
e(ssimp[sound_grammar_to_parser_thm_def]);
e(intros);
e(ASSUME_TAC prefix_sound_sound_thm);
e(ASSUME_TAC prefix_sound_grammar_to_parser_thm);
e(ssimp[prefix_sound_sound_thm_def]);
e(ssimp[prefix_sound_grammar_to_parser_thm_def]);
e(ssimp[LET_THM] THEN NO_TAC);
val sound_grammar_to_parser_thm = top_thm();


(*  + admits *)

g `
! pt lc lc'. admits lc pt ==> (! x. MEM x lc' ==> MEM x lc) ==> admits lc' pt
`;
val tm = ``! lc lc'. admits lc pt ==> (! x. MEM x lc' ==> MEM x lc) ==> admits lc' pt``;
want `! pt. ^tm`; e(INIT_TAC);
want `! n pt. (parse_tree_size pt = n) ==> ^tm`; e(tac[]);
e(completeInduct_on `n`);
e(intros);
e(Cases_on `pt`);
 (* NODE *)
 e(Cases_on `p`);
 e(RENAME_TAC [``q:nonterm``|->``nt:nonterm``,``r:parse_tree list``|->``pts:parse_tree list``]);
 have `! pt. MEM pt pts ==> ^tm`;
  e(tac[MEM_pt_pts_parse_tree_size]);
 e(Q_THIN_TAC `! m:num. _`);
 e(Q_THIN_TAC `parse_tree_size (NODE (nt,pts)) = n`);
 e(ssimp[admits_def_2,LET_THM]);
 cr(); e(tac[]);
 e(ssimp[listTheory.EVERY_MEM]);
 have `! x. MEM x ((nt,THE (substring_of (NODE (nt,pts))))::lc') ==> MEM x ((nt,THE (substring_of (NODE (nt,pts))))::lc)`;
  e(ssimp[]); e(tac[]);
 e(tac[]);

 (* LF *)
 e(ssimp[admits_def_2] THEN NO_TAC);
val admits_subset = top_thm();

g `
! pt lc lc' s_pt.
admits lc pt
==> (substring_of pt = SOME s_pt)
==> (FILTER (\ (nt,s). low s_pt <= low s /\ high s <= high s_pt) lc' = lc) (* the entries that matter are those st ... <= ... etc *)
==> admits lc' pt
`;
val tm = ``
! lc lc' s_pt.
admits lc pt
==> (substring_of pt = SOME s_pt)
==> (FILTER (\ (nt,s). low s_pt <= low s /\ high s <= high s_pt) lc' = lc)
==> admits lc' pt
``;
want `! pt. ^tm`; e(INIT_TAC);
want `! n pt. (parse_tree_size pt = n) ==> ^tm`; e(tac[]);
e(completeInduct_on `n`);
e(intros);
e(Cases_on `pt`);
 (* NODE *)
 e(Cases_on `p`);
 e(RENAME_TAC [``q:nonterm``|->``nt:nonterm``,``r:parse_tree list``|->``pts:parse_tree list``]);
 have `! pt. MEM pt pts ==> ^tm`;
  e(tac[MEM_pt_pts_parse_tree_size]);
 e(Q_THIN_TAC `! m:num. _`);
 e(Q_THIN_TAC `parse_tree_size (NODE (nt,pts)) = n`);
 e(ssimp[admits_def_2,LET_THM]);
 cr();
  e(SYM_TAC `_ = lc`);
  e(ssimp[listTheory.MEM_FILTER,arith_simps] THEN NO_TAC);

  e(ssimp[]);
  e(ssimp[listTheory.EVERY_MEM]);
  e(intros);
  xal `a`;
  e(ssimp[]);
  xal `a`;
  e(ssimp[]);
  xal `((nt,s_pt)::lc')`;
  have `? s_a. substring_of a = SOME s_a`;
   have `EVERY IS_SOME (MAP (\a. substring_of a) pts)`; e(tac[hereditary_lemmas]);
   e(ssimp[listTheory.EVERY_MEM]);
   xal `substring_of a`;
   e(ssimp[listTheory.MEM_MAP]);
   il 0; e(tac[]);
   e(Cases_on `substring_of a` THEN ssimp[] THEN NO_TAC);
  e(elims);
  xal `s_a`;
  e(ssimp[]);
  e(Cases_on `low s_a <= low s_pt /\ high s_pt <= high s_a`);
   e(ssimp[]);
   have `(low s_a = low s_pt) /\ (high s_a = high s_pt)`;
    e(tac[low_s_pt_low_s_pt'_high_s_pt_high_s_pt',le_thms]);
   e(ssimp[] THEN NO_TAC);

   e(ssimp[]);
   il 0; defer(); e(tac[]);
   have `! x. MEM x (FILTER (\ (nt,s). low s_a <= low s /\ high s <= high s_a) lc') ==> MEM x (FILTER (\ (nt,s). low s_pt <= low s /\ high s <= high s_pt) lc')`;
    e(ssimp[listTheory.MEM_FILTER]);
    e(intros);
    e(Cases_on `x`);
    e(ssimp[]);
    e(tac[low_s_pt_low_s_pt'_high_s_pt_high_s_pt',le_thms]);
   have `admits lc a`;
    have `! x. MEM x lc ==> MEM x ((nt,s_pt)::lc)`; e(ssimp[] THEN NO_TAC);
    e(tac[admits_subset]);
   e(tac[admits_subset]);

 (* LF *)
 e(ssimp[admits_def_2]);
val admits_strengthen = top_thm();


g `
admits lc (NODE (nt,pts))
==> (substring_of (NODE (nt,pts)) = SOME s_pt)
==> MEM pt' pts
==> (concatenate_two s_pt s_rem' = SOME s_tot')
==> admits ((nt,s_tot')::lc) pt'
`;
(* if s_pt = s_tot', we have it from admits, otherwise all proper_subtrees have a smaller string that s_tot; *)
e(intros);
e(Cases_on `s_pt = s_tot'`);
 e(ssimp[]);
 e(ssimp[admits_def_2,LET_THM]);
 e(ssimp[listTheory.EVERY_MEM] THEN NO_TAC);

 e(ssimp[]);
 e(ssimp[admits_def_2,LET_THM]);
 e(ssimp[listTheory.EVERY_MEM]);
 xal `pt'`;
 e(ssimp[]);
 have `admits lc pt'`;
  have `! x. MEM x lc ==> MEM x ((nt,s_pt)::lc)`;
   e(ssimp[] THEN NO_TAC);
  e(tac[admits_subset]);
 have `admits (FILTER (\ (nt,s). low s_pt <= low s /\ high s <= high s_pt) lc) pt'`;
  have `! x. MEM x (FILTER (\ (nt,s). low s_pt <= low s /\ high s <= high s_pt) lc) ==> MEM x lc`; e(ssimp[listTheory.MEM_FILTER] THEN NO_TAC);
  e(tac[admits_subset]);
 have `? s_pt'. substring_of pt' = SOME s_pt'`;
  have `EVERY IS_SOME (MAP ( \ a. substring_of a) pts)`; e(tac[hereditary_lemmas]);
  e(ssimp[listTheory.EVERY_MEM]);
  xal `substring_of pt'`;
  e(ssimp[listTheory.MEM_MAP]);
  il 0; e(tac[]);
  e(Cases_on `substring_of pt'` THEN ssimp[] THEN NO_TAC);
 e(elims);
 have `! x. MEM x (FILTER (\ (nt,s). low s_pt' <= low s /\ high s <= high s_pt') ((nt,s_tot')::lc)) ==> MEM x (FILTER (\ (nt,s). low s_pt <= low s /\ high s <= high s_pt) lc)`;
  e(intros);
  e(ssimp[]);
  have `low s_pt <= low s_pt' /\ high s_pt' <= high s_pt`;
   e(tac[low_s_pt_low_s_pt'_high_s_pt_high_s_pt']);
  have `~ (high s_tot' <= high s_pt')`;
   ir();
   have `high s_tot' = high s_pt`; e(tac[concatenate_two_SOME,le_thms]);
   have `low s_tot' = low s_pt`; e(tac[concatenate_two_SOME,low_s_pt_low_s_pt'_high_s_pt_high_s_pt',le_thms]);
   have `string s_tot' = string s_pt`; e(tac[concatenate_two_SOME,low_s_pt_low_s_pt'_high_s_pt_high_s_pt']);
   e(MY_ASSUME_TAC(INST [``s:substring``|->``s_pt:substring``] tcases_2));
   e(elims);
   e(MY_ASSUME_TAC(INST [``s:substring``|->``s_tot':substring``] tcases_2));
   e(elims);
   e(ssimp[low_def,high_def,string_def,LET_THM]);
   e(ssimp ty_substring_simps THEN NO_TAC);
  e(ssimp[]);
  have `MEM x (FILTER (\(nt,s). low s_pt' <= low s /\ high s <= high s_pt') lc)`; e(INIT_TAC);
  want `MEM x (FILTER (\(nt,s). low s_pt <= low s /\ high s <= high s_pt) lc)`; e(INIT_TAC);
  e(ssimp[listTheory.MEM_FILTER]);
  e(Cases_on `x`);
  e(ssimp[]);
  e(tac[le_thms]);
 e(tac[admits_strengthen,admits_subset]);
val admits_weaken = top_thm();
(* FIXME actually another form of strengthen *)



(*  + admits_thm *)

g `
(x <> NONE) = (IS_SOME x)
`;
e(Cases_on `x` THEN ssimp[]);
val NOT_NONE_EQ_IS_SOME = top_thm();

g `
admits_thm
`;
e(ssimp[admits_thm_def]);
val tm = ``! lc.
  (! pt'. MEM pt' (subtrees pt) ==> is_NODE pt' /\ IS_SOME (substring_of pt') ==> ~ MEM (dest_NT (root pt'),THE(substring_of pt')) lc)
  ==> wf_parse_tree pt ==> good_tree pt ==> admits lc pt
``;
want `! pt. ^tm`;
 e(intros);
 xal `pt`;
 xal `[]:local_context`;
 e(ssimp[] THEN NO_TAC);
want `! n pt. (parse_tree_size pt = n) ==> ^tm`; e(tac[]);
e(completeInduct_on `n`);
e(intros);
e(Cases_on `pt`);
 (* NODE *)
 val here_1229 = p(); dropn 1; add(here_1229);
 e(Cases_on `p`);
 e(RENAME_TAC [``q:nonterm``|->``nt:nonterm``,``r:parse_tree list``|->``pts:parse_tree list``]);
 e(ssimp[admits_def_2]);
 e(MY_LET_INTRO_TAC);
 al `NODE(nt,pts)`;
 e(ASM_CONV_TAC (fn ths => SIMP_CONV (srw_ss()) [subtrees_def_2]) 0);
 e(ssimp[is_NODE_def_2,dest_NT_def_2,root_def_2]);
 e(ssimp[listTheory.EVERY_MEM]);
 have `~MEM(nt,s_pt) lc`; 
  e(ssimp[wf_parse_tree_def]);
  e(ssimp[NOT_NONE_EQ_IS_SOME] THEN NO_TAC);
 e(ssimp[]);  
 e(intros);
 e(RENAME_TAC [``a:parse_tree``|->``pt':parse_tree``]);
 xal `parse_tree_size pt'`;
 il 0; e(tac[MEM_pt_pts_parse_tree_size]);
 xal `pt'`;
 il 0; e(ssimp[] THEN NO_TAC);
 xal `((nt,s_pt)::lc)`;
 have `! pt''. MEM pt'' (subtrees pt') ==> MEM pt'' (proper_subtrees (NODE(nt,pts)))`;
  e(intros);
  e(ssimp[proper_subtrees_def,subtrees_def_2]);
  e(ssimp[listTheory.MEM_FLAT]);
  er `subtrees pt'`;
  e(ssimp[listTheory.MEM_MAP]);
  e(tac[]);
 il 1;
  ar();
  ir();
  ir();
  e(REORDER_TAC `!pt'. MEM pt' (subtrees (NODE (nt,pts))) ==> is_NODE pt' /\ IS_SOME (substring_of pt') ==> ~MEM (dest_NT (root pt'),THE (substring_of pt')) lc`);
  xal `pt''`;
  il 0; 
   e(ssimp[proper_subtrees_def]); 
   xal `pt''`; 
   e(ssimp[subtrees_def_2] THEN NO_TAC);
  il 0; e(INIT_TAC);
  ir();
  e(ssimp[]);
  have `~MEM (nt,s_pt) lc`; e(INIT_TAC);
  have `is_NODE pt'' /\ (dest_NT (root pt'') = nt) /\ IS_SOME (substring_of pt'') /\ (THE (substring_of pt'') = s_pt)`; e(tac[]);
  want `F`; e(INIT_TAC);
  (* so pt'' has same nonterminal and substring as NODE(nt,pts)... but NODE(nt,pts) is good *)
  e(ssimp[good_tree_def_2]);
  e(ssimp[listTheory.EVERY_MEM]);
  e(REORDER_TAC `!pt. MEM pt (subtrees (NODE (nt,pts))) ==> ~bad_root pt`);
  xal `NODE(nt,pts)`;
  e(ssimp[subtrees_def_2]);
  il 0; defer(); e(INIT_TAC);
  want `bad_root (NODE (nt,pts))`; e(INIT_TAC);
  e(ssimp[bad_root_def]);
  e(ssimp[listTheory.EXISTS_MEM]);
  er `pt''`;
  val here_1272 = p(); dropn 1; add(here_1272);
  cr();
   e(tac[]);
   
   e(ssimp[matches_pt_def]);
   e(Cases_on `substring_of pt''` THEN ssimp[]);
   e(ssimp[wf_parse_tree_def]);
   e(ssimp[NOT_NONE_EQ_IS_SOME]);
   e(Cases_on `substring_of (NODE(nt,pts))` THEN ssimp[]);
   e(Cases_on `pt''` THEN ssimp[]);
    defer();
    e(Cases_on `p`);
    e(ssimp[is_NODE_def] THEN NO_TAC);
   e(Cases_on `p`);
   e(ssimp[root_def_2,dest_NT_def] THEN NO_TAC);

 val here_1759 = p(); dropn 1; add(here_1759);
 il 0; e(tac[hereditary_lemmas]);
 il 0; e(tac[hereditary_lemmas]);
 e(INIT_TAC);

 (* LF *)
 e(Cases_on `p`);
 e(ssimp[admits_def_2,LET_THM] THEN NO_TAC);
val admits_thm = top_thm();

(*  + good_tree_exists_thm *)

g `
good_tree_exists_thm
`;
e(ssimp[good_tree_exists_thm_def]);
(* go for well-founded induction on size of tree *)
ar(); ar();
want `
! n pt. (parse_tree_size pt = n) ==>
pt IN (pts_of ss_of_tm g) ==> let pt' = mk_good_tree pt in pt' IN (pts_of ss_of_tm g) /\ (matches_pt pt pt') /\ (good_tree pt')
`;
 e(ssimp[LET_THM]);
 e(tac[]);
e(completeInduct_on `n`);
e(intros);
e(elims);
e(Cases_on `pt`);
 (* NODE *)
 e(Cases_on `p`);
 e(RENAME_TAC [``q:ty_nonterm``|->``nt:nonterm``,``r:parse_tree list``|->``pts:parse_tree list``]);
 e(MY_LET_INTRO_TAC);
 have `mk_good_tree (NODE (nt,pts)) = pt'`; e(INIT_TAC);
 val here_405 = p(); dropn 1; add(here_405);
 (* every proper descendant has a parse tree with no bad nodes *)
 have `! pt. MEM pt pts ==> let pt' = mk_good_tree pt in pt' IN (pts_of ss_of_tm g) /\ matches_pt pt pt' /\ good_tree pt'`;
  e(intros);
  xal `parse_tree_size pt`;
  il 0; e(tac[MEM_pt_pts_parse_tree_size]);
  xal `pt`;
  e(ssimp[]);
  il 0; e(tac[hereditary_lemmas]);
  e(ssimp[] THEN NO_TAC);
 e(Q_THIN_TAC `! m. m < n ==> _`);
 e(ssimp[mk_good_tree_def_2,LET_THM]);
 e(ssimp[]);
 want `pt' IN pts_of ss_of_tm g /\ matches_pt (NODE (nt,pts)) pt' /\ good_tree pt'`; e(INIT_TAC);
 have `matches_pt (NODE (nt,pts)) (NODE (nt,MAP (\a. mk_good_tree a) pts))`; 
  e(ssimp[matches_pt_def_2,root_def,dest_NODE_def]);
  want `substring_of (NODE (nt,MAP (\a. mk_good_tree a) pts)) = substring_of (NODE (nt,pts))`; e(INIT_TAC);
  e(ssimp[substring_of_def_2]);
  have `? ss. MAP (\ a. substring_of a) pts = ss`; e(tac[]);
  have `? ss'. MAP (\ a. substring_of a) (MAP (\a. mk_good_tree a) pts) = ss'`; e(tac[]); (* FIXME actually ss' = ss *)
  e(elims);
  e(ssimp[LET_THM]);
  have `EVERY IS_SOME ss`; 
   e(ssimp[listTheory.EVERY_MEM]);   
   e(intros);
   e(RENAME_TAC [``e:substring option``|->``sopt:substring option``]);
   e(SYM_TAC `_=ss`);
   e(ssimp[listTheory.MEM_MAP]);
   e(RENAME_TAC [``a:parse_tree``|->``pt:parse_tree``]);
   e(ssimp[]);
   have `pt IN pts_of ss_of_tm g`; e(tac[hereditary_lemmas]);
   e(assimp[SPECIFICATION,pts_of_def]0);   
   e(ssimp[wf_parse_tree_def]);
   e(ssimp[NOT_NONE_EQ_IS_SOME] THEN NO_TAC);
  have `EVERY IS_SOME ss'`;
   e(ssimp[listTheory.EVERY_MEM]);   
   e(intros);
   e(RENAME_TAC [``e:substring option``|->``sopt':substring option``]);
   e(SYM_TAC `_=ss'`);
   e(ssimp[listTheory.MEM_MAP]);
   e(RENAME_TAC [``a:parse_tree``|->``pt1':parse_tree``,``a':parse_tree``|->``pt1:parse_tree``]);
   xal `pt1`; 
   e(ssimp[]);
   have `IS_SOME (substring_of pt1)`; 
    e(SYM_TAC `_=ss`);
    e(ssimp[]);
    e(ssimp[listTheory.MEM_MAP]);
    e(tac[]);
   e(ssimp[matches_pt_def] THEN NO_TAC);
  e(ssimp[]);
  want `ss' = ss`; e(tac[]);
  e(SYM_TAC `_=ss`);
  e(SYM_TAC `_=ss'`);
  e(ssimp[]);
  have `MAP (\ a. substring_of a) (MAP (\ a. mk_good_tree a) pts) = MAP ((\ a. substring_of a) o (\ a. mk_good_tree a)) pts`;
   e(ssimp[rich_listTheory.MAP_o] THEN NO_TAC);
  e(ssimp[]);
  e(MATCH_MP_TAC' listTheory.MAP_CONG);
  e(ssimp[]);
  e(intros);
  e(RENAME_TAC [``x:parse_tree``|->``pt1:parse_tree``]);
  xal `pt1`;
  e(ssimp[matches_pt_def] THEN NO_TAC);
 e(Cases_on `bad_root (NODE (nt,MAP (\a. mk_good_tree a) pts))`);
  val here_1830 = p(); dropn 1; add(here_1830);
  (* bad_root *)
  defer();
  e(ssimp[]);
  have `~ bad_root pt'`; e(INIT_TAC);
  (* do matches first *)
  have `matches_pt (NODE (nt,pts)) pt'`; e(INIT_TAC);
  e(ssimp[]);
  have `pt' IN (pts_of ss_of_tm g)`;
   e(SYM_TAC `_ = pt'`);
   e(SIMP_TAC (std_ss) [pts_of_def,SPECIFICATION]);
   e(REORDER_TAC `NODE (nt,pts) IN pts_of ss_of_tm g`);
   e(assimp [pts_of_def,SPECIFICATION] 0);
   e(ssimp[]);
   have `(\a. mk_good_tree a) = mk_good_tree`; e(tac[]);
   e(ssimp[]);
   cr();
    have `wf_parse_tree (NODE (nt,pts))`; e(INIT_TAC);
    want `wf_parse_tree (NODE (nt,MAP mk_good_tree pts))`; e(ssimp[] THEN NO_TAC);
    e(ssimp[wf_parse_tree_def_2]);
    e(ssimp[matches_pt_def_2]);
    e(ssimp[wf_prs_tree_def_2]);
    e(ssimp[listTheory.EVERY_MEM]);
    e(ssimp[listTheory.MEM_MAP]);
    e(intros);
    e(elims);
    e(ssimp[]);
    e(REORDER_TAC `! pt. MEM pt pts ==> P`);
    xal `y`;
    e(assimp[pts_of_def,SPECIFICATION]0);
    e(ssimp[wf_parse_tree_def] THEN NO_TAC);

    e(ssimp[subtrees_def_2]);
    e(intros);
    dl();
     (* pt'' = NODE *)
     e(ssimp[]);
     xal `NODE(nt,pts)`;
     e(ssimp[]);
     have `(MAP root (MAP mk_good_tree pts)) = MAP root pts`; 
      want `MAP (root o mk_good_tree) pts = MAP root pts`; e(ssimp[rich_listTheory.MAP_o] THEN NO_TAC);
      e(MATCH_MP_TAC' listTheory.MAP_CONG);
      e(ssimp[]);
      e(intros);
      xal `x`;
      e(ssimp[matches_pt_def] THEN NO_TAC);
     e(ssimp[] THEN NO_TAC);

     (* MEM pt'' (FLAT (MAP (\a. subtrees a) (MAP mk_good_tree pts))) *)
     (* so use the induction hyp on ... *)
     e(ssimp[listTheory.MEM_FLAT,listTheory.MEM_MAP]);
     (* FIXME need that the subtrees of mk_good_tree are subset of subtrees of orig *)
     e(REORDER_TAC `!pt. MEM pt pts ==> P`);
     xal `y`;
     e(ssimp[]);
     e(REORDER_TAC `mk_good_tree y IN pts_of ss_of_tm g`);
     e(assimp[pts_of_def,SPECIFICATION]0);
     e(ssimp[] THEN NO_TAC);
  (* lastly do good tree *)
  val here_1889 = p(); dropn 1; add(here_1889);
  e(ssimp[]);
  want `good_tree pt'`; e(INIT_TAC);
  e(SYM_TAC `_ = pt'`);
  e(ssimp[good_tree_def_2]);
  e(ssimp[subtrees_def_2]);
  e(ssimp[listTheory.EVERY_MEM]);
  e(ssimp[listTheory.MEM_FLAT,listTheory.MEM_MAP]);
  ar();
  ir();
  e(elims);
  e(RENAME_TAC [``a':parse_tree``|->``pt2:parse_tree``]);
  e(ssimp[]);
  have `good_tree (mk_good_tree pt2)`; e(tac[]);
  e(Q_THIN_TAC `! pt. MEM pt pts ==> _`);
  e(ssimp[good_tree_def]);
  e(ssimp[listTheory.EVERY_MEM] THEN NO_TAC);

  val here_535 = p(); dropn 1; add(here_535);
  (* bad_root (NODE (nt,MAP (\a. mk_good_tree a) pts)) *)
  e(ssimp[]);
  have `? P. (\ x. MEM x (TL (subtrees (NODE (nt,MAP (\a. mk_good_tree a) pts)))) /\ matches_pt (NODE (nt,MAP (\a. mk_good_tree a) pts)) x) = P`; e(tac[]);
  e(elims);
  e(ssimp[]);
  have `P pt'`;
   have `? x. P x`; 
    e(ssimp[bad_root_def]);
    e(ssimp[listTheory.EXISTS_MEM]);
    e(ssimp[proper_subtrees_def]);
    e(SYM_TAC `_=P` THEN ssimp[]);
    e(tac[]);
   (* choice *)
   e(ssimp[proper_subtrees_def]);
   e(tac[EXISTS_CHOICE]); 
  e(SYM_TAC `_ = P`);
  e(ssimp[]);
  e(REMOVE_VAR_TAC `P`);
  e(Q_THIN_TAC `CHOICE _ = pt'`);
  have `matches_pt (NODE (nt,MAP (\a. mk_good_tree a) pts)) pt'`; e(INIT_TAC);
  have `matches_pt (NODE (nt,pts)) (NODE (nt,MAP (\a. mk_good_tree a) pts))`; e(INIT_TAC); 
  have `matches_pt (NODE (nt,pts)) pt'`; e(ssimp[matches_pt_def] THEN NO_TAC);
  e(ssimp[]);
  e(REORDER_TAC `MEM pt' (TL (subtrees (NODE (nt,MAP (\a. mk_good_tree a) pts))))`);
  e(ssimp[subtrees_def_2]);
  e(ssimp[listTheory.MEM_FLAT]);
  have `MAP (\ a. subtrees a) (MAP (\ a. mk_good_tree a) pts) = MAP ((\ a. subtrees a) o (\ a. mk_good_tree a)) pts`;
   e(ssimp[rich_listTheory.MAP_o] THEN NO_TAC);
  e(ssimp[]);
  e(ssimp[listTheory.MEM_MAP]);
  e(ssimp[]);
  e(RENAME_TAC [``y:parse_tree``|->``pt:parse_tree``]);
  xal `pt`;
  e(ssimp[]);
  have `mk_good_tree pt IN pts_of ss_of_tm g`; e(INIT_TAC);
  have `MEM pt' (subtrees (mk_good_tree pt))`; e(INIT_TAC);
  e(ssimp[MEM_subtrees_MEM_proper_subtrees]);
  dl();
   e(tac[]);

   e(tac[good_tree_proper_subtrees,pts_of_proper_subtrees]);

 (* LF *)
 e(ssimp[LET_THM]);
 e(ssimp[mk_good_tree_def_2]);
 e(Cases_on `p`);
 e(ssimp[]);
 e(ssimp[matches_pt_def_2,good_tree_def_2]);
 e(ssimp[good_tree_def,bad_root_def,LET_THM,subtrees_def_2,proper_subtrees_def] THEN NO_TAC);
val good_tree_exists_thm = top_thm();


(*  + main_thm *)

g `
! ss_of_tm gtp.
let P = (\ pt sym s_pt s_rem s_tot lc.
  let p = gtp sym in
  wf_parse_tree pt 
  /\ pt IN pts_of ss_of_tm g 
  /\ (root pt = sym) /\ (substring_of pt = SOME s_pt) 
  /\ (concatenate_two s_pt s_rem = SOME s_tot) 
  /\ admits lc pt 
  ==>
  MEM (pt,s_rem) (p <|lc1 := lc; sb1 := s_tot|>))
in
! lc lc_s_tot pts alt nt s_pts s_rem s_tot.
pts <> [] ==>
(MAP root pts = alt) ==>
(concatenate_two s_pts s_rem = SOME s_tot) ==>
(!pt. MEM pt pts ==> wf_parse_tree pt /\ pt IN pts_of ss_of_tm g /\ admits ((nt,lc_s_tot)::lc) pt) ==>
(!pt. MEM pt pts ==> !sym s_pt s_rem s_tot lc. P pt sym s_pt s_rem s_tot lc) ==>
EVERY IS_SOME (MAP (\a. substring_of a) pts) ==>
(concatenate_list (MAP THE (MAP (\a. substring_of a) pts)) = SOME s_pts) ==>
MEM (pts,s_rem) (then_list (MAP gtp alt) <|lc1 := (nt,lc_s_tot)::lc; sb1 := s_tot|>)
`; 
e(intros);
e(MY_LET_INTRO_TAC);
ar();
ar();
e(Induct_on `pts`);
 (* NIL *)
 e(ssimp[] THEN NO_TAC);

 val here_827 = p(); dropn 1; add(here_827);
 e(intros);
 e(Cases_on `alt`);
  e(ssimp[] THEN NO_TAC);
 e(RENAME_TAC [``h':symbol``|->``a:symbol``, ``t:symbol list``|->``alt:symbol list``]);
 e(RENAME_TAC [``h:parse_tree``|->``pt:parse_tree``]);
 e(RENAME_TAC [``s_pts:substring``|->``s_ptpts:substring``]);
 have `? s_pt. THE (substring_of pt) = s_pt`; e(tac[]);
 e(elims);
 want `MEM (pt::pts,s_rem) (then_list (MAP (gtp) (a::alt)) <|lc1 := (nt,lc_s_tot)::lc; sb1 := s_tot|>)`; e(INIT_TAC);
 (* the problem here is that pts may be [], in which case we can't talk about s_pts *)
 (* NB s_pts is meaningless unless pts <> []; we use it just as an abbreviation *)
 have `? s_pts. (THE (concatenate_list (MAP THE (MAP (\a. substring_of a) pts)))) = s_pts`; e(tac[]);
 e(elims);
 have `? s_rem'. (case pts of [] -> s_rem || _ -> THE(concatenate_two s_pts s_rem))  = s_rem'`; e(tac[]); (* s_rem' is what is left after parsing pt *)
 e(elims);
 have `pts <> [] ==> (THE(concatenate_two s_pts s_rem) = s_rem')`; e(Cases_on `pts` THEN ssimp[] THEN NO_TAC);
 val here_1166 = p(); dropn 1; add(here_1166);
 have `pts <> [] ==> (concatenate_two s_pts s_rem = SOME s_rem')`;
  ir();
  e(ssimp[]);
  have `(string s_pts = string s_rem) /\ (high s_pts = low s_rem)`;
   have `concatenate_list (s_pt::MAP THE (MAP (\a. substring_of a) pts)) = SOME s_ptpts`; e(INIT_TAC);
   e(ssimp[concatenate_list_def_2]);
   e(Cases_on `MAP THE (MAP (\a. substring_of a) pts)`); e(ssimp[] THEN NO_TAC);
   e(ssimp[]);
   e(Cases_on `concatenate_list (h::t)`); e(ssimp[] THEN NO_TAC);
   e(ssimp[]);
   have `concatenate_two s_ptpts s_rem = SOME s_tot`; e(INIT_TAC);
   have `concatenate_two s_pt s_pts = SOME s_ptpts`; e(INIT_TAC);
   e(tac[concatenate_two_SOME]);
  e(ssimp[concatenate_two_def] THEN NO_TAC);
 val here_1192 = p(); dropn 1; add(here_1192);
 have `concatenate_two s_pt s_rem' = SOME s_tot`;
  e(Cases_on `pts = []`);
   e(ssimp[]);
   e(ssimp[concatenate_list_def] THEN NO_TAC);

   e(ssimp[]);
   have `concatenate_two s_pt s_pts = SOME s_ptpts`;
    e(ssimp[concatenate_list_def_2]);
    e(Cases_on `MAP THE (MAP (\a. substring_of a) pts)`); e(ssimp[] THEN NO_TAC);
    e(ssimp[]);
    e(Cases_on `concatenate_list (h::t)` THEN ssimp[] THEN NO_TAC);
   have `concatenate_two s_ptpts s_rem = SOME s_tot`; e(INIT_TAC);
   e(ssimp[]);
   e(MY_ASSUME_TAC(INST [``s:substring``|->``s_pt:substring``] tcases_2));
   e(elims);
   e(MY_ASSUME_TAC(INST [``s:substring``|->``s_pts:substring``] tcases_2));
   e(elims);
   e(MY_ASSUME_TAC(INST [``s:substring``|->``s_rem':substring``] tcases_2));
   e(elims);
   e(MY_ASSUME_TAC(INST [``s:substring``|->``s_rem:substring``] tcases_2));
   e(elims);
   e(MY_ASSUME_TAC(INST [``s:substring``|->``s_tot:substring``] tcases_2));
   e(elims);
   e(MY_ASSUME_TAC(INST [``s:substring``|->``s_ptpts:substring``] tcases_2));
   e(elims);
   e(ssimp[concatenate_two_def,string_def,low_def,high_def,LET_THM]);
   e(ssimp ty_substring_simps);
   have `wf_substring (a'''',b,b''') /\ wf_substring (a'''',b',c''')`; e(tac[wf_substring_thms]);
   e(ssimp ty_substring_simps THEN NO_TAC);
 want `MEM (pt,s_rem') (gtp a <| lc1 := (nt,lc_s_tot)::lc; sb1 := s_tot |>)`;
  e(Cases_on `pts = []`);
   (* pts = [] *)
   e(ssimp[]);
   e(SYM_TAC `_ = alt`);
   e(ssimp[]);
   e(REMOVE_VAR_TAC `alt`);
   have `MEM (pt,s_rem') (gtp a <|lc1 := (nt,lc_s_tot)::lc; sb1 := s_tot |>)`; e(INIT_TAC);
   want `MEM ([pt],s_rem') (then_list [gtp a] <|lc1 := (nt,lc_s_tot)::lc; sb1 := s_tot|>)`; e(INIT_TAC);
   e(ssimp[then_list_def,myrr_def,mythen_def,always_def,LET_THM,substr_def]);
   e(ssimp[listTheory.MEM_MAP]);
   e(ssimp[listTheory.MEM_FLAT]);
   e(ssimp[listTheory.MEM_MAP]);
   er `((pt,[]),s_rem)`;
   e(ssimp[]);
   er `[((pt,[]),s_rem)]`;
   e(ssimp[]);
   er `(pt,s_rem)`;
   e(ssimp[] THEN NO_TAC);

   val here_988 = p(); dropn 1; add(here_988);
   (* pts <> [] *)
   have `(concatenate_list (MAP THE (MAP (\a. substring_of a) pts)) = SOME s_pts)`;
    e(REORDER_TAC `concatenate_list (MAP THE (MAP (\a. substring_of a) (pt::pts))) = SOME s_ptpts`);
    e(ssimp[concatenate_list_def_2]);
    e(Cases_on `(MAP THE (MAP (\a. substring_of a) pts))`); e(ssimp[] THEN NO_TAC);
    e(ssimp[]);
    e(Cases_on `concatenate_list (h::t)` THEN ssimp[] THEN NO_TAC);
   have `MEM (pts,s_rem) (then_list (MAP (gtp) alt) <|lc1 := (nt,lc_s_tot)::lc; sb1 := s_rem'|>)`;
    xal `alt`;
    xal `nt`;
    xal `s_pts`;
    xal `s_rem`;
    xal `s_rem'`;
    il 0; e(ssimp[] THEN NO_TAC);
    il 0; e(ssimp[] THEN NO_TAC);
    il 0; e(ssimp[] THEN NO_TAC); (* concatenate_two s_pts s_rem = SOME s_rem' *)
    il 0; e(ssimp[] THEN NO_TAC);
    il 0; e(ssimp[] THEN NO_TAC);
    il 0; e(ssimp[] THEN NO_TAC);
    il 0; e(INIT_TAC); (* (concatenate_list (MAP THE (MAP (\a. substring_of a) pts)) = SOME s_pts) *)
    e(INIT_TAC);
   e(Q_THIN_TAC `! alt nt s_pts s_rem s_tot. _`);
   e(Q_THIN_TAC `_ = s_rem'`);
   e(ssimp[]);
   want `MEM (pt::pts,s_rem) (then_list (gtp a::MAP (gtp) alt) <|lc1 := (nt,lc_s_tot)::lc; sb1 := s_tot|>)`; e(INIT_TAC);
   e(MATCH_MP_TAC' (INST [``substring_of':parse_tree->substring option``|->``substring_of:parse_tree->substring option``] MEM_CONS_then_list));
   e(cintros);
    (* 3 subgoals *)
    e(tac[]); (* concatenate_list (MAP THE (MAP substring_of pts)) = SOME s_pts *)

    want `MEM (pt,THE (concatenate_two s_pts s_rem)) (gtp a <|lc1 := (nt,lc_s_tot)::lc; sb1 := s_tot|>)`; e(INIT_TAC);
    e(ssimp[] THEN NO_TAC);

    want `MEM (pts,s_rem) (then_list (MAP (gtp) alt) <|lc1 := (nt,lc_s_tot)::lc; sb1 := THE (concatenate_two s_pts s_rem)|>)`; e(INIT_TAC);
    have `MEM (pts,s_rem) (then_list (MAP (gtp) alt) <|lc1 := (nt,lc_s_tot)::lc; sb1 := s_rem'|>)`; e(INIT_TAC);
    e(ssimp[] THEN NO_TAC);

 val here_1829 = p(); dropn 1; add(here_1829);
 e(REORDER_TAC `!pt'. MEM pt' (pt::pts) ==> !sym s_pt s_rem s_tot lc. P pt' sym s_pt s_rem s_tot lc`);
 xal `pt`;
 il 0; e(ssimp[] THEN NO_TAC);
 xal `root pt`;
 xal `s_pt`;
 xal `s_rem'`;
 xal `s_tot`;
 xal`(nt,lc_s_tot)::lc`;
 e(SYM_TAC `_ = P`);
 e(assimp[LET_THM]1);
 e(SYM_TAC `P = _`);
 il 1;
  e(ssimp[root_def]);
  have `substring_of pt = SOME s_pt`;
   (* s_pt cannot be NONE *)
   e(Cases_on `substring_of pt`);
    e(ssimp[] THEN NO_TAC);

    e(ssimp[] THEN NO_TAC);
  e(ssimp[]);

 have `MEM (pt,s_rem') (gtp (root pt) <|lc1 := (nt,lc_s_tot)::lc; sb1 := s_tot |>)`; e(INIT_TAC);
 want `MEM (pt,s_rem') (gtp a <|lc1 := (nt,lc_s_tot)::lc; sb1 := s_tot |>)`; e(INIT_TAC);
 have `a = root pt`; e(ssimp[root_def] THEN NO_TAC);
 e(ssimp[] THEN NO_TAC);
val pre_main_thm = top_thm();

g `
main_thm
`;
e(ssimp[main_thm_def]);
ar();
ar();
have `? P. (\ pt sym s_pt s_rem s_tot lc.
    let p = grammar_to_parser p_of_tm g sym in
    let ss_of_tm = ss_of_tm_of p_of_tm in
     wf_p_of_tm p_of_tm /\ wf_grammar g /\ wf_parse_tree pt /\ pt IN pts_of ss_of_tm g /\ (root pt = sym) /\ (substring_of pt = SOME s_pt) /\
     (concatenate_two s_pt s_rem = SOME s_tot) /\ (* good_tree pt /\ *) admits lc pt ==>
     MEM (pt,s_rem) (p <|lc1 := lc; sb1 := s_tot|>))
    = P
`;
 e(tac[]);
e(elims);
val tm = ``! (sym:symbol) (s_pt:substring) (s_rem:substring) (s_tot:substring) (lc:local_context). P (pt:parse_tree) sym s_pt s_rem s_tot lc``;
want `! pt. ^tm`; e(tac[]);
want `! n pt. (parse_tree_size pt = n) ==> ^tm`; e(tac[]);
e(completeInduct_on `n`);
e(intros);
have `? p.  grammar_to_parser p_of_tm g sym = p`; e(tac[]);
e(elims);
e(Cases_on `pt`);
 (* NODE *)
 e(Cases_on `p'`);
 e(RENAME_TAC [``q:nonterm``|->``nt':nonterm``,``r:parse_tree list``|->``pts:parse_tree list``]);
 have `! pt. MEM pt pts ==> ^tm`; e(tac[MEM_pt_pts_parse_tree_size]);
 e(Q_THIN_TAC `! m:num. _`);
 e(Q_THIN_TAC `parse_tree_size (NODE (nt',pts)) = n`);
 e(SYM_TAC `_ = P`);
 e(ASM_SIMP_TAC (std_ss) []);
 e(SYM_TAC `_ = P`);
 e(MY_LET_INTRO_TAC);
 e(SYM_TAC `p = p'`);
 e(intros);
 e(ssimp[]);
 e(Cases_on `sym`); e(ssimp[root_def_2] THEN NO_TAC);
 e(RENAME_TAC [``t:nonterm``|->``nt:nonterm``]);
 have `nt' = nt`; e(ssimp[root_def,dest_NT_def] THEN NO_TAC);
 e(ssimp[]);
 e(Q_THIN_TAC `root _ = NT nt`);
 e(REMOVE_VAR_TAC `nt'`);
 e(Q_THIN_TAC `p' = p`);
 e(REORDER_TAC `_ = p`);
 e(SYM_TAC `_ = p`);
 e(ASM_SIMP_TAC (std_ss) []);
 e(SYM_TAC `_ = p`);
 e(ssimp[grammar_to_parser_def_2]);
 have `? alt. MAP root pts = alt`; e(tac[]);
 e(elims);
 have `? rhs. MEM alt rhs /\ MEM (nt,rhs) g`;
  e(REORDER_TAC `_ IN pts_of _ g`);
  e(assimp[SPECIFICATION,pts_of_def]0);
  xal `NODE(nt,pts)`;
  il 0; e(ssimp[subtrees_def_2] THEN NO_TAC);
  e(ssimp[]);
  e(ssimp[listTheory.EXISTS_MEM]);
  e(Cases_on `e`);
  e(ssimp[]);
  e(tac[]);
 e(elims);
 have `? rules. FILTER (\(a,b). a = nt) g = rules`; e(tac[]);
 e(elims);
 have `MEM (nt,rhs) rules`;
  have `(\ (a,b). a = nt) (nt,rhs)`; e(ssimp[] THEN NO_TAC);
  e(tac[listTheory.MEM_FILTER]);
 have `? alts1. FLAT (MAP SND rules) = alts1`; e(tac[]);
 e(elims);
 have `MEM alt alts1`;
  have `SND (nt,rhs) = rhs`; e(ssimp[] THEN NO_TAC);
  e(tac[listTheory.MEM_MAP, listTheory.MEM_FLAT]);
 have `? alts2. MAP (MAP (\sym'. grammar_to_parser p_of_tm g sym')) alts1 = alts2`; e(tac[]);
 e(elims);
 have `MEM (MAP (\sym'. grammar_to_parser p_of_tm g sym') alt) alts2`;
  e(tac[listTheory.MEM_MAP]);
 e(ssimp[LET_THM]);
 e(ssimp[check_and_upd_lctxt_def]);
 (* establish some simple facts that help us discharge the assums of pre_main_thm *)
 val here_2855 = p(); dropn 1; add(here_2855);
 have `pts <> []`; e(ssimp[wf_parse_tree_def,wf_prs_tree_def_2] THEN NO_TAC);
 have `(!pt. MEM pt pts ==> wf_parse_tree pt /\ pt IN pts_of ss_of_tm g)`;
  e(intros);
  e(RENAME_TAC [``pt:parse_tree``|->``pt':parse_tree``]);
  e(MY_ASSUME_TAC (INST [``ss:(term -> substring set)``|->``(ss_of_tm_of p_of_tm)``,``pt:parse_tree``|->``pt':parse_tree``] hereditary_lemmas));
  e(ssimp[] THEN NO_TAC);
 have `EVERY IS_SOME (MAP (\a. substring_of a) pts)`; e(tac[hereditary_lemmas]);
 have `(concatenate_list (MAP THE (MAP (\a. substring_of a) pts)) = SOME s_pt)`; 
  e(ssimp[substring_of_def_2,LET_THM] THEN NO_TAC);
 (* now do some case splitting *)
 e(Cases_on `EXISTS ($= (nt,s_tot)) lc`);
  e(ssimp[LET_THM]);
  e(Cases_on `len s_tot = 0`);
   (* contradiction with admits *)
   e(REORDER_TAC `admits _ _`);
   e(ssimp[admits_def_2,LET_THM]);
   have `s_pt = s_tot`;
    e(REORDER_TAC `concatenate_two s_pt s_rem = SOME s_tot`);
    e(REORDER_TAC `len s_tot = 0`);
    e(MY_ASSUME_TAC(INST [``s:substring``|->``s_pt:substring``] tcases_2));
    e(elims);
    e(MY_ASSUME_TAC(INST [``s:substring``|->``s_rem:substring``] tcases_2));
    e(elims);
    e(MY_ASSUME_TAC(INST [``s:substring``|->``s_tot:substring``] tcases_2));
    e(elims);
    e(ssimp[]);
    e(ssimp ty_substring_simps);
    e(ssimp[concatenate_two_def,low_def,high_def,string_def,len_def,LET_THM]);
    e(ssimp ty_substring_simps);
    have `wf_substring (a',b,c')`; e(tac[wf_substring_thms]);
    e(ssimp ty_substring_simps);
    e(ssimp[wf_substring_def]);
    e(Q.PAT_UNDISCH_TAC `c'' - b'' = 0`);
    e(Q.PAT_UNDISCH_TAC `b'' <= c''`);
    e(Q_THIN_TAC `_ <= STRLEN _`);
    e(Q_THIN_TAC `_ <= STRLEN _`);
    e(Q.PAT_UNDISCH_TAC `b'' <= (b':num)`);
    e(Q.PAT_UNDISCH_TAC `b'' <= (b':num)`);
    e(numLib.ARITH_TAC);
   e(ssimp[]);
   e(ssimp[listTheory.EXISTS_MEM] THEN NO_TAC);

   (* len s_tot <> 0 *)
   val here_2711 = p(); dropn 1; add(here_2711);
   have `len s_tot <> 0`; e(INIT_TAC);
   e(ssimp[]);
   e(ssimp[ignr_last_def]);
   e(ssimp[substr_def]);
   e(ssimp[LET_THM]);
   e(ssimp[lift_def]);
   e(ssimp[]);
   e(ssimp[update_lctxt_def]);
   (* show that we can indeed dec_high 1 *)
   (* we know the context contains (nt,s_tot), so we know s_pt can't be s_tot (since the context admits pt); so s_rem <> 0, dec_high is welldefined, and inc_high o dec_high is id *)
   have `s_pt <> s_tot`;
    ir();
    e(REORDER_TAC `admits lc (NODE(nt,pts))`);
    e(REORDER_TAC `EXISTS ($= (nt,s_tot)) lc`);
    e(ssimp[admits_def_2,LET_THM]);
    e(ssimp[listTheory.EXISTS_MEM] THEN NO_TAC);
   have `len s_rem <> 0`;
    e(REORDER_TAC `concatenate_two s_pt s_rem = SOME s_tot`);
    e(ssimp[concatenate_two_def]);
    e(MY_ASSUME_TAC(INST [``s:substring``|->``s_pt:substring``] tcases_2));
    e(elims);
    e(MY_ASSUME_TAC(INST [``s:substring``|->``s_rem:substring``] tcases_2));
    e(elims);
    e(MY_ASSUME_TAC(INST [``s:substring``|->``s_tot:substring``] tcases_2));
    e(elims);
    e(ssimp[]);
    e(ssimp[low_def,high_def,string_def,len_def,LET_THM]);
    e(ssimp ty_substring_simps);
    have `wf_substring (a',b,c')`; e(tac[wf_substring_thms]);
    e(ssimp ty_substring_simps);
    e(ssimp[wf_substring_def]);
    e(Q.PAT_UNDISCH_TAC `b' <= c''`);      
    e(Q.PAT_UNDISCH_TAC `b' <> c''`);      
    e(Q.PAT_UNDISCH_TAC `b' <> c''`);      
    e(numLib.ARITH_TAC);
   have `? s_tot'. dec_high 1 s_tot = s_tot'`; e(tac[]);
   e(elims);
   have `? s_rem'. dec_high 1 s_rem = s_rem'`; e(tac[]);
   e(elims);
   e(ssimp[]);
   have `concatenate_two s_pt s_rem' = SOME s_tot'`;
    e(ssimp[]);
    e(MY_ASSUME_TAC(INST [``s:substring``|->``s_rem:substring``] tcases_2));
    e(elims);
    e(MY_ASSUME_TAC(INST [``s:substring``|->``s_tot:substring``] tcases_2));
    e(elims);
    e(MY_ASSUME_TAC(INST [``s:substring``|->``s_pt:substring``] tcases_2));
    e(elims);
    e(ssimp[]);
    e(SYM_TAC `_ = s_rem'`);
    e(SYM_TAC `_ = s_tot'`);
    e(ssimp[concatenate_two_def,string_def,low_def,high_def,len_def,LET_THM]);
    e(ssimp ty_substring_simps);
    e(ssimp[dec_high_def,LET_THM]);
    e(ssimp ty_substring_simps);
    have `wf_substring (a,b'',c)`; e(tac[wf_substring_thms]);
    e(ssimp ty_substring_simps);
    have `wf_substring (a',b,c' - 1)`; e(tac[wf_substring_thms]); 
    e(ssimp ty_substring_simps THEN NO_TAC);
   want `MEM (NODE (nt,pts),s_rem) (MAP (\(e,s). (e,inc_high 1 s)) (or_list (MAP (then_list2 nt) alts2) <|lc1 := (nt,s_tot')::lc; sb1 := s_tot'|>))`; e(INIT_TAC);
   (* depends on (len s_rem <> 0), ie (s_pt <> s_tot) *)
   e(ssimp[listTheory.MEM_MAP]);
   er `(NODE (nt,pts),s_rem')`;
   e(ssimp[]);
   cr();
    want `s_rem = inc_high 1 s_rem'`; e(INIT_TAC);
    e(tac[inc_high_one_dec_high_one]);

    val here_2939 = p(); dropn 1; add(here_2939);
    want `MEM (NODE (nt,pts),s_rem') (or_list (MAP (then_list2 nt) alts2) <|lc1 := (nt,s_tot')::lc; sb1 := s_tot'|>)`; e(INIT_TAC);
    e(ssimp[SYM(SPEC_ALL or_list_thm)]);
    er `then_list2 nt (MAP (\sym'. grammar_to_parser p_of_tm g sym') alt)`;
    cr();
     e(ssimp[listTheory.MEM_MAP]);
     e(tac[]);
    e(ssimp[then_list_two_def,myrr_def]);
    e(ssimp[listTheory.MEM_MAP]);
    er `(pts,s_rem')`;
    cr(); e(ssimp[] THEN NO_TAC);
    want `MEM (pts,s_rem') (then_list (MAP (\sym'. grammar_to_parser p_of_tm g sym') alt) <|lc1 := (nt,s_tot')::lc; sb1 := s_tot'|>)`; e(INIT_TAC);
    (* invoke our subinduction *)
    e(MY_ASSUME_TAC pre_main_thm);
    xal `ss_of_tm_of p_of_tm`;
    xal `grammar_to_parser p_of_tm g`;    
    e(ssimp[LET_THM]);
    xal `lc`;
    xal `s_tot'`;
    xal `pts`;
    xal `nt`;
    xal `s_pt`;
    xal `s_rem'`;    
    xal `s_tot'`;
    il 0; e(INIT_TAC);
    il 0; e(INIT_TAC);
    il 0; 
     e(intros);
     e(ssimp[]);
     want `admits ((nt,s_tot')::lc) pt`; e(INIT_TAC);
     have `admits ((nt,s_pt)::lc) pt`; e(tac[hereditary_lemmas,optionTheory.THE_DEF]);
     e(tac[admits_weaken]);
    il 0; e(SYM_TAC `_=P`); e(ssimp[] THEN NO_TAC);
    il 0; e(INIT_TAC); 
    il 0; e(INIT_TAC);
    have `(\ sym'. grammar_to_parser p_of_tm g sym') = grammar_to_parser p_of_tm g`; e(tac[]);
    e(ssimp[] THEN NO_TAC);

  val here_2775 = p(); dropn 1; add(here_2775);
  have `~ (EXISTS ($= (nt,s_tot)) lc)`; e(INIT_TAC);
  e(ASM_SIMP_TAC (srw_ss()) []);
  e(ssimp[LET_THM]);
  e(ssimp[update_lctxt_def]);
  want `MEM (NODE (nt,pts),s_rem) (or_list (MAP (then_list2 nt) alts2) <|lc1 := (nt,s_tot)::lc; sb1 := s_tot|>)`; e(INIT_TAC);
  e(ssimp[SYM(SPEC_ALL or_list_thm)]);
  er `then_list2 nt (MAP (\sym'. grammar_to_parser p_of_tm g sym') alt)`;
  cr();
   e(ssimp[listTheory.MEM_MAP]);
   e(tac[]);
  e(ssimp[then_list_two_def,myrr_def]);
  e(ssimp[listTheory.MEM_MAP]);
  er `(pts,s_rem)`;
  cr(); e(ssimp[] THEN NO_TAC);
  want `MEM (pts,s_rem) (then_list (MAP (\sym'. grammar_to_parser p_of_tm g sym') alt) <|lc1 := (nt,s_tot)::lc; sb1 := s_tot|>)`; e(INIT_TAC);
    (* invoke our subinduction *)
  e(MY_ASSUME_TAC pre_main_thm);
  xal `ss_of_tm_of p_of_tm`;
  xal `grammar_to_parser p_of_tm g`;    
  e(ssimp[LET_THM]);
  xal `lc`;
  xal `s_tot`;
  xal `pts`;
  xal `nt`;
  xal `s_pt`;
  xal `s_rem`;    
  xal `s_tot`;
  il 0; e(INIT_TAC);
  il 0; e(INIT_TAC);
  il 0; 
   e(intros);
   e(ssimp[]);
   want `admits ((nt,s_tot)::lc) pt`; e(INIT_TAC);
   have `admits ((nt,s_pt)::lc) pt`; e(tac[hereditary_lemmas,optionTheory.THE_DEF]);
   e(tac[admits_weaken]);
  il 0; e(SYM_TAC `_=P`); e(ssimp[] THEN NO_TAC);
  il 0; e(INIT_TAC); 
  il 0; e(INIT_TAC);
  have `(\sym'. grammar_to_parser p_of_tm g sym') = grammar_to_parser p_of_tm g`; e(tac[]);
  e(ssimp[] THEN NO_TAC);

 (* LF - trivial, maybe lift earlier? *)
 val here_1338 = p(); dropn 1; add(here_1338);
 e(Cases_on `p'`);
 e(RENAME_TAC [``q:term``|->``tm:term``,``r:substring``|->``s_lf:substring``]);
 e(ssimp[]);
 e(SYM_TAC `_ = P`);
 e(ssimp[]);
 e(ssimp[LET_THM]);
 e(intros);
 e(elims);
 e(SYM_TAC `_ = p`);
 e(ssimp[]);
 e(ssimp[grammar_to_parser_def_2]);
 e(ssimp[root_def]);
 e(SYM_TAC `_ = sym`);
 e(ssimp[]);
 e(REORDER_TAC `LF (tm,s_lf) IN pts_of (ss_of_tm_of p_of_tm) g`);
 e(assimp[pts_of_def,SPECIFICATION]0);
 e(ssimp[subtrees_def_2]);
 e(ssimp[myrr_def]);
 e(ssimp[listTheory.MEM_MAP]);
 er `(s_lf,s_rem)`;
 e(ssimp[]);
 e(ssimp[ss_of_tm_of_def,LET_THM]);
 have `s_lf IN {s | ? i s'. MEM (s,s') (p_of_tm tm i)}`; 
  e(SIMP_TAC (std_ss) [SPECIFICATION]);
  e(INIT_TAC);
 e(ssimp[GSPECIFICATION]);
 e(RENAME_TAC [``s':substring``|->``s_rem':substring``]);
 have `? lc' s_tot'. i = <| lc1 := lc'; sb1 := s_tot' |>`; e(tac[icases_thm]);
 e(elims);
 e(ssimp[]);
 have `MEM (s_lf,s_rem') (p_of_tm tm <| lc1 := lc'; sb1 := s_tot' |>)`; e(INIT_TAC);
 want `MEM (s_lf,s_rem) (p_of_tm tm <|lc1 := lc; sb1 := s_tot|>)`; e(INIT_TAC);
 e(ssimp[substring_of_def_2]);
 e(ssimp[wf_p_of_tm_def,LET_THM]);
 e(tac[]);
val main_thm = top_thm();

(*  + corollary *)

g `
corollary
`;
e(ssimp[corollary_def]);
e(intros);
e(MY_LET_INTRO_TAC);
e(intros);
e(ssimp[prefix_complete_def]);
e(intros);
e(CONV_TAC (MINISCOPE_EXISTS_CONV true));
e(intros);
e(elims);
have `? pt'. pt' IN pts_of (ss_of_tm_of p_of_tm) g /\ (matches_pt pt pt') /\ good_tree pt'`;
 e(tac[good_tree_exists_thm,good_tree_exists_thm_def]);
e(elims);
er `pt'`;
e(ssimp[]);
e(ASSUME_TAC main_thm);
e(ssimp[main_thm_def]);
xal `p_of_tm`;
xal `g`;
e(ssimp[LET_THM]);
xal `pt'`;
xal `s_pt`;
xal `s_rem:substring`;
xal `s_tot`;
xal `[]:local_context`;
il 0; e(cintros);
 (* 5 subgoals *)
 e(ssimp[pts_of_def,SPECIFICATION] THEN NO_TAC);

 e(INIT_TAC);

 e(ssimp[matches_pt_def] THEN NO_TAC);

 e(tac[concatenate_two_SOME]); 

 have `wf_parse_tree pt'`;
  e(ssimp[pts_of_def,SPECIFICATION] THEN NO_TAC);
 e(tac[admits_thm,admits_thm_def]);
e(ssimp[toinput_def,matches_pt_def] THEN NO_TAC);
val corollary = top_thm();

(*  + prefix_complete_complete_thm *)

g `
prefix_complete_complete_thm
`;
e(ssimp[prefix_complete_complete_thm_def]);
e(intros);
e(ssimp[complete_def,prefix_complete_def]);
e(intros);
e(elims);
e(CONV_TAC (MINISCOPE_EXISTS_CONV true));
e(intros);
e(elims);
e(MY_ASSUME_TAC(INST [``s:substring``|->``s:substring``] tcases_2));
e(elims);
e(ssimp[]);
e(REMOVE_VAR_TAC `s`);
have `wf_substring (a,c,c)`; e(tac[wf_substring_thms]);
xal `myabs (a,b,c)`;
xal `myabs (a,b,c)`;
xal `myabs (a,c,c)`;
xal `pt`;
e(elims);
il 5;
 e(ssimp[]);
 e(ssimp[concatenate_two_def]);
 e(ssimp[string_def,high_def,low_def,LET_THM]);
 e(ssimp ty_substring_simps THEN NO_TAC);
e(elims);
er `pt'`;
e(ssimp[simple_parser_of_def]);
e(ssimp[listTheory.MEM_MAP]);
er `(pt',myabs (a,c,c))`;
e(ssimp[]);
e(ssimp[listTheory.MEM_FILTER]);
e(ssimp[matches_pt_def] THEN NO_TAC);
val prefix_complete_complete_thm = top_thm();


(*  + complete_grammar_to_parser_thm *)

g `
complete_grammar_to_parser_thm
`;
e(ssimp[complete_grammar_to_parser_thm_def]);
e(intros);
e(MY_LET_INTRO_TAC);
e(intros);
have `prefix_complete (ss_of_tm_of p_of_tm) g sym p`;
 e(ASSUME_TAC corollary);
 e(ssimp[corollary_def,LET_THM]);
 e(tac[]);
e(ASSUME_TAC prefix_complete_complete_thm);
e(ssimp[prefix_complete_complete_thm_def] THEN NO_TAC);
val complete_grammar_to_parser_thm = top_thm();

(* * end *)

val _ = List.map save_thm [
  ("sound_grammar_to_parser_thm", sound_grammar_to_parser_thm),
  ("complete_grammar_to_parser_thm",complete_grammar_to_parser_thm)
];
  

val _ = export_theory();

(*

Local Variables:
outline-regexp: "^(\\* +[*+.]+ "
fill-column: 80
mode: outline-minor
mode: hi-lock
sml-program-name: "/tmp/dist/HOL/bin/hol"
End:

*)

