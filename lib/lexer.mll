{
 open Parser
 exception Eof
 exception LexicalError
 let opt_debug = ref false
 let verbose s = if !opt_debug then print_endline s else ()
 let comment_depth = ref 0
 let keyword_tbl = Hashtbl.create 31
 let _ = List.iter (fun (keyword, tok) -> Hashtbl.add keyword_tbl keyword tok)
        [
            ("if", IF);
            ("then", THEN);
            ("else", ELSE);
            ("while", WHILE);
            ("do", DO);
            ("true", TRUE);
            ("false", FALSE);
            ("read", READ);
            ("goto", GOTO)
        ] 
} 

let blank = [' ' '\n' '\t' '\r']+
let id = ['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '\'' '0'-'9' '_']*
let number = ['0'-'9']+

rule start =
 parse blank { start lexbuf }
     | "(*" { comment_depth :=1;
              comment lexbuf;
              start lexbuf }
     | number { 
        let n = Lexing.lexeme lexbuf in
        verbose n;
        NUM (int_of_string n)
       }
     | id {
        let id = Lexing.lexeme lexbuf in
        verbose id;
        try Hashtbl.find keyword_tbl id
        with Not_found -> ID id
       }
     | "*" {verbose "*"; STAR}
     | "+" {verbose "+"; PLUS}
     | "-" {verbose "-"; MINUS}
     | "||" {verbose "||"; ORELSE}
     | "!" {verbose "!"; NOT}
     | "&&" {verbose "&&"; ANDALSO}
     | "&" {verbose "&"; AT}
     | "<" {verbose "<"; LT}
     | ">" {verbose ">"; GT}
     | ":=" {verbose ":="; COLONEQ}
     | ";" { verbose ";"; SEMICOLON}
     | "(" { verbose "("; LP}
     | ")" { verbose ")"; RP}
     | eof { verbose "eof"; EOF}
     | _ {raise LexicalError}

and comment = parse
     "(*" {comment_depth := !comment_depth+1; comment lexbuf}
   | "*)" {comment_depth := !comment_depth-1;
           if !comment_depth > 0 then comment lexbuf }
   | eof {raise Eof}
   | _   {comment lexbuf}
