

(* hol_light library stuff *)

let rec itlist f l b =
  match l with
    [] -> b
  | (h::t) -> f h (itlist f t b);;

let rec forall p l =
  match l with
    [] -> true
  | h::t -> p(h) & forall p t;;

let rec filter p l =
  match l with
    [] -> l
  | h::t -> let t' = filter p t in
            if p(h) then if t'==t then l else h::t'
            else t';;

let rec mem x lis =
  match lis with
    [] -> false
  | (h::t) -> Pervasives.compare x h = 0 or mem x t;;

let insert x l =
  if mem x l then l else x::l;;

let union l1 l2 = itlist insert l1 l2;;

let unions l = itlist union l [];;

let intersect l1 l2 = filter (fun x -> mem x l2) l1;;

let subtract l1 l2 = filter (fun x -> not (mem x l2)) l1;;

let subset l1 l2 = forall (fun t -> mem t l2) l1;;

let set_eq l1 l2 = subset l1 l2 & subset l2 l1;;

let report s =
  Format.print_string s; Format.print_newline();;

let time f x =
  let start_time = Sys.time() in
  try let result = f x in
      let finish_time = Sys.time() in
      report("CPU time (user): "^(string_of_float(finish_time -. start_time)));
      result
  with e ->
      let finish_time = Sys.time() in
      Format.print_string("Failed after (user) CPU time of "^
                          (string_of_float(finish_time -. start_time))^": ");
      raise e;;


(* basic parsing types *)

type term = string
type nonterm = string
type symbol = NT of nonterm | TM of term
type rhs = (symbol list) list

type parse_rule = nonterm * rhs

type grammar = parse_rule list




type earley_item = { nt2: nonterm; a2: symbol list; b2: symbol list; i2:int; j2:int }

module OrderedEarleyItem = 
  struct
    type t = earley_item
    let compare x y  = Pervasives.compare x y
  end

type earley_key = int * nonterm

module OrderedEarleyKey = 
  struct 
    type t = earley_key
    let compare x y  = Pervasives.compare x y
  end

module EarleyKeyMap = Map.Make(OrderedEarleyKey)


(* version using sets *)

module EarleyItemSet = Set.Make(OrderedEarleyItem)

type earley_item_set = EarleyItemSet.t

type loop_state = {
  g4:grammar;
  string4:string; (* the character at this posn in the input *)
  caneps4: nonterm -> bool;
  done4: earley_item_set;
  todo4: earley_item_set;
  next4: earley_item_set;
  n4: int;
  s4: earley_item_set EarleyKeyMap.t;
}


module A = struct

  let empty = EarleyItemSet.empty

  let mem x xs = EarleyItemSet.mem x xs
    
  let is_empty x = EarleyItemSet.is_empty x
    
  let add x xs = EarleyItemSet.add x xs
    
  let remove x xs = EarleyItemSet.remove x xs
    
  let itset f xs acc = EarleyItemSet.fold f xs acc

  let subtract = EarleyItemSet.diff

  let choose s = EarleyItemSet.choose s

  let todo_add itm s =
    if mem itm s.done4 then 
      s 
    else 
      {s with todo4=(add itm s.todo4)}
        
end




(* version using lists, for debugging purposes; uncomment to use*)

(*
type loop_state = {
  g4:grammar;
  string4:string; (* the character at this posn in the input *)
  caneps4: nonterm -> bool;
  done4: earley_item list;
  todo4: earley_item list;
  next4: earley_item list;
  n4: int;
  s4: earley_item list EarleyKeyMap.t;
}


module A = struct

  let empty=[]

  let mem x xs = mem x xs

  let is_empty x = (x=[])
  
  let add x xs = x::xs
  
  let remove x xs = subtract xs [x]
  
  let itset f xs acc = itlist f xs acc
  
  let subtract = subtract
  
  let choose s = List.hd s
  
  let todo_add itm s =
    if mem itm s.done4 then 
      s 
    else 
      {s with todo4=(add itm s.todo4)}

end

*)


(* invariant: each rule has reached to the point of processing s0.n4 char *)
let loop1 s0 = (match A.is_empty s0.todo4 with | true -> s0 | false -> (
  (* invariant: nothing gets added to todo4 that is already in done4? *)
  let itm = A.choose s0.todo4 in
  let s1 = {s0 with todo4=(A.remove itm s0.todo4); done4=(A.add itm s0.done4)} in
  if itm.j2 = s1.n4+1 then {s1 with next4=(A.add itm s1.next4)} (* process at next stage *) else
  let s2 = (match itm.b2 with
    | [] -> ( (* the rule is complete *)
      if itm.i2 = s1.n4 && itm.j2=s1.n4 then 
        s1 (* no need to process further ? handled by explicit caneps *) 
      else (
        (* invariant: j2 is s1.n4 and i2 is <j2 *)
        (* FIXME is this complete rule with i2=n+1 ie the current stage? yes *)
        (* we need to get the blocked rules and add them to todo *)
        let (nt,i) = (itm.nt2,itm.i2) in
        let bs = EarleyKeyMap.find (i,nt) s1.s4 in
        let f1 bitm s =
          (* for each blocked itm *)
          let bitm' = {bitm with 
            a2 = (List.hd bitm.b2)::bitm.a2;
            b2 = List.tl bitm.b2;
            j2 = itm.j2;
          } in
          A.todo_add bitm' s
        in
        A.itset f1 bs s1))
    | NT nt::bs -> (
      (* invariant: j2=s1.n4 *)
      (* first take care of eps rules *)
      let s1 = if s1.caneps4 nt then A.todo_add {itm with a2=(NT nt)::itm.a2; b2=bs} s1 else s1 in
      let rs = List.filter (fun (nt',rhs) -> nt' = nt) s1.g4 in
      let alts = List.concat (List.map snd rs) in
      let itms = List.map (fun alt -> { nt2=nt; a2=[]; b2=alt; i2=itm.j2; j2=itm.j2 }) alts in
      let f1 itm s = 
        let s = A.todo_add itm s in
        s
      in
      let s1 = itlist f1 itms s1 in
      (* also need to update the blocked *)
      let (nt,i) = (nt,itm.j2) in (* note the j - perhaps we should always use this var name for blocked? *)
      let s1 = {s1 with s4=(EarleyKeyMap.add (i,nt) (A.add itm (EarleyKeyMap.find (i,nt) s1.s4)) s1.s4) } in
      s1)
    | TM tm::bs -> (
      (* FIXME can we assume j2=s1.n4? *)
      (* assume tm is not eps - this is encoded in caneps4 *)      
      if 
        (itm.j2=s1.n4) 
        && (s1.n4 < String.length s1.string4) 
        && (tm=(String.sub s1.string4 s1.n4 1)) 
      then 
        let itm = {itm with a2=(TM tm)::itm.a2; b2=(List.tl itm.b2); j2=itm.j2+1} in
        {s1 with next4=(A.add itm s1.next4)} 
      else 
        s1))
  in
  s2))

let step1 s = {s with
  todo4=s.next4;
  done4=A.empty;
  next4=A.empty;
  n4=s.n4+1;
  s4=EarleyKeyMap.add (s.n4+1,"E") A.empty s.s4;
}

let rec earley s = 
  if A.is_empty s.todo4 && A.is_empty s.next4 then s 
  else if A.is_empty s.todo4 then earley (step1 s) 
  else earley (loop1 s)
    

(* example *)

(* E -> E E E | "x" | "" ; the eps production is handled via caneps4 *)
let myg = [("E",[[NT "E"; NT "E"; NT "E"];[TM "x"]])]

let i0 = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"

let tmps = {
  g4=myg;
  string4=i0; (* the character at this posn in the input *)
  caneps4= (fun _ -> true);
  done4= A.empty;
  todo4= A.add {nt2="E";a2=[];b2=[NT "E"];i2=0;j2=0} A.empty;
  next4= A.empty;
  n4= 0;
  s4=(EarleyKeyMap.add (0,"E") A.empty EarleyKeyMap.empty);  
}

let tmps = time earley tmps (* should take about 1s *)
let _ = EarleyItemSet.elements tmps.done4

