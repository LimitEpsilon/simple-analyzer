(*
 * program
 *)
  
type id = string
type exp =
  | NUM of int
  | VAR of id
  | DEREF of id
  | AT of id
  | ADD of exp * exp
  | MULT of exp * exp
  | MINUS of exp
  | TRUE
  | FALSE
  | READ
  | NOT of exp
  | ANDALSO of exp * exp
  | ORELSE of exp * exp
  | LESS of exp * exp
  
type cmd =
  | SEQ of labelled_cmd * labelled_cmd        (* sequence *)
  | IF of exp * labelled_cmd * labelled_cmd   (* if-then-else *)
  | WHILE of exp * labelled_cmd      (* while *)
  | GOTO of exp
  | ASSIGN of id * exp      (* assgin to variable *)
  | PTRASSIGN of id * exp

and labelled_cmd =
  | LBL of int * cmd

type program = labelled_cmd

let rec exp_to_str = function
  | NUM i -> string_of_int i
  | VAR x -> x
  | DEREF x -> "*" ^ x
  | AT x -> "&" ^ x
  | ADD (e1, e2) -> "(" ^ exp_to_str e1 ^ " + " ^ exp_to_str e2 ^ ")"
  | MULT (e1, e2) -> "(" ^ exp_to_str e1 ^ " * " ^ exp_to_str e2 ^ ")"
  | MINUS e -> "-(" ^ exp_to_str e ^ ")"
  | TRUE -> "true"
  | FALSE -> "false"
  | READ -> "read()"
  | NOT e -> "not" ^ exp_to_str e
  | ANDALSO (e1, e2) ->  "(" ^ exp_to_str e1 ^ " && " ^ exp_to_str e2 ^ ")"
  | ORELSE (e1, e2) -> "(" ^ exp_to_str e1 ^ " || " ^ exp_to_str e2 ^ ")"
  | LESS (e1, e2) -> "(" ^ exp_to_str e1 ^ " < " ^ exp_to_str e2 ^ ")"

let indent_char = " "
let rec indent lvl =
  if lvl <= 0
  then ""
  else indent_char ^ indent (lvl - 1)

let rec cmd_to_str lvl = function LBL (l, cmd) ->
  let lbl = string_of_int l ^ ": " in
  match cmd with
  | ASSIGN (x, e) -> indent lvl ^ lbl ^ x ^ " := " ^ exp_to_str e
  | PTRASSIGN (x, e) -> indent lvl ^ lbl ^ "*" ^ x ^ " := "^ exp_to_str e
  | SEQ (c1, c2) ->
    indent lvl ^ lbl ^ "SEQ\n" ^
    cmd_to_str (lvl + 1) c1 ^ ";\n" ^
    cmd_to_str (lvl + 1) c2
  | IF (e, c1, c2) -> 
    indent lvl ^ lbl ^ "IF\n" ^
    indent (lvl + 1) ^ "if " ^ exp_to_str e ^ " then\n" ^
    cmd_to_str (lvl + 1) c1 ^ " else\n" ^
    cmd_to_str (lvl + 1) c2
  | WHILE (e, c) ->
    indent lvl ^ lbl ^ "WHILE\n" ^
    indent (lvl + 1) ^ "while " ^ exp_to_str e ^ " do (\n" ^
    cmd_to_str (lvl + 1) c ^ ")" 
  | GOTO e ->
    indent lvl ^ lbl ^
    "goto " ^ exp_to_str e

let pp c =  print_endline (cmd_to_str 0 c)
