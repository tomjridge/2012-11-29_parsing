

(* of no interest elsewhere, so we don't move to top *)
type ty_cl_args = { input: string; grammar: string; alg: string; output:bool; memo:bool; basedir:string }

(* precedence to earlier args *)
let rec parse_CL = fun i -> (
  let f1 (f,xs) cl = (match (f,xs) with
    | ("-basedir",[a]) -> {cl with basedir=a } (* only for main_gen *)
    | ("-output",["true"]) -> {cl with output=true }
    | ("-output",["false"]) -> {cl with output=false }
    | ("-memo",["true"]) -> {cl with memo=true }
    | ("-memo",["false"]) -> {cl with memo=false }
    | ("-f",[a]) -> {cl with input=a }
    | ("-g",[a]) -> {cl with grammar=a }
    | ("-alg",[a]) -> {cl with alg=a }
    | _ -> (failwith ("parse_CL: unrecognized flag/arg combination: "^f^" "^(String.concat " " xs))))
  in
  let cl0 = { input="/tmp/input.txt"; grammar="/tmp/grammar.g"; alg="cf"; output=true; memo=true; basedir="." } in
  let sep = a "\x00" in
  (((listof parse_FLARGS sep) **> parse_EOF) >> (fun (xs,_) -> itlist f1 xs cl0))) i

let args = 
  let argv = List.tl (Array.to_list (Sys.argv)) in
(*  let _ = print_endline ("Command line: "^(String.concat " " argv)) in *)
  let (r,_) = List.hd (parse_CL (toinput (full (String.concat "\x00" argv)))) in
  r


let main =
  let txt = read_file_as_string args.input in
  let p = parse_start in
  let _ = p (toinput (full txt)) in
  ()

