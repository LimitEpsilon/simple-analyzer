open Absint
open Syntax
open Semantics

let src = ref ""
let opt_pp = ref false
let opt_intp = ref false
let opt_cintp = ref false
let opt_analyze = ref false

let main () =
  Arg.parse
    [
      ("-debug", Arg.Unit (fun _ -> Lexer.opt_debug := true), "debug parsing");
      ("-pp", Arg.Unit (fun _ -> opt_pp := true), "print pgm");
      ("-intp", Arg.Unit (fun _ -> opt_intp := true), "interpreter");
      ("-cintp", Arg.Unit (fun _ -> opt_cintp := true), "collecting interpreter");
      ("-analyze", Arg.Unit (fun _ -> opt_analyze := true), "analyzer");
    ]
    (fun x -> src := x)
    ("Usage : " ^ Filename.basename Sys.argv.(0) ^ " [-option] [filename] ");
  let lexbuf =
    Lexing.from_channel (if !src = "" then stdin else open_in !src)
  in
  let pgm = Parser.program Lexer.start lexbuf in
  if !opt_pp then
    let _ = print_endline "=== Printing Input Program ===" in
    pp pgm
  else if !opt_intp then
    let result = intp pgm in
    print_endline (Printer.string_of_mem result)
  else if !opt_cintp then
    let results = cintp pgm in
    print_endline (Printer.string_of_col results)
  else if !opt_analyze then
    let results = analysis pgm in
    print_endline (Printer.string_of_asem results)
  else
    print_endline
      "Please provide one of options! (-pp, -intp, -cintp, -analyze)"

let _ = main ()
