(*******************************************************************************
 * Time-stamp: <2015-10-16 CEST 10:56:59 David Chemouil>
 * 
 * Electrum Analyzer 
 * Copyright (C) 2014-2015 Onera
 * Authors: 
 *   David Chemouil 
 * 
 * This file is part of the Electrum Analyzer.
 * 
 * The Electrum Analyzer is free software: you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * The Electrum Analyzer is distributed in the hope that it will be
 * useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with the Electrum Analyzer.  If not, see
 * <http://www.gnu.org/licenses/>.
 ******************************************************************************)


{
(* BEGIN HEADER *)

open Batteries
open Util
open Lexing
open Parser

(* local to this module *)
exception Lexing_error of string Lazy.t

let line_column pos =
  (pos.pos_lnum,  pos.pos_cnum - pos.pos_bol)

let error lexbuf msg =
  let lsp = lexeme_start_p lexbuf in
  let line_start, col_start = line_column lsp in
  let line_end, col_end = line_column (lexeme_end_p lexbuf) in
  let s = lazy (Printf.sprintf "line %d, column %d - line %d, column %d: %s"
                  line_start col_start line_end col_end msg) in
  raise (Lexing_error s)
      
let tokenize t lexbuf =
  (t, lexeme_start_p lexbuf, lexeme_end_p lexbuf)

(* to deal with "_static" in the hack *)
let _static_as_id = Ast_ident.make "_static"

(* END HEADER *)
}

let newline = ('\010' | '\013' | "\013\010")

let whitespace = [ ' ' '\t' ]

let digit = [ '0'-'9' ]

let number = (digit | [ '1'-'9'] digit*)
                           
let letter = [ 'A'-'Z' 'a'-'z' ]

let identifier = letter (letter | digit | '_')*

let comment_line = ("//" | "--")

let reserved_symbol = [ '$' '%' '\\' '`' ]
                 
rule main tokens = parse
| reserved_symbol as c
    { error lexbuf (Printf.sprintf "Reserved character: '%c'" c)}
| newline
    { new_line lexbuf; main tokens lexbuf }
| whitespace+
    { main tokens lexbuf }
| number as i
    {
      try
        main (tokenize (NUMBER (int_of_string i)) lexbuf :: tokens) lexbuf
      with Failure _ ->
        error lexbuf ("Invalid integer constant '" ^ i ^ "'")
    }
| "!="
    { main (tokenize NEQ lexbuf :: tokens) lexbuf }
| "'"
    { main (tokenize PRIME lexbuf :: tokens) lexbuf }
| "@"
    { main (tokenize AT lexbuf :: tokens) lexbuf }
| "&"
    { main (tokenize INTER lexbuf :: tokens) lexbuf }
| "->"
    { main (tokenize ARROW lexbuf :: tokens) lexbuf }
| "<:"
    { main (tokenize LPROJ lexbuf :: tokens) lexbuf }
| ":>"
    { main (tokenize RPROJ lexbuf :: tokens) lexbuf }
| "."
    { main (tokenize DOT lexbuf :: tokens) lexbuf }
| "~"
    { main (tokenize TILDE lexbuf :: tokens) lexbuf }
| "*"
    { main (tokenize STAR lexbuf :: tokens) lexbuf }
| "^"
    { main (tokenize CARET lexbuf :: tokens) lexbuf }
| "Int"
    { main (tokenize INT lexbuf :: tokens) lexbuf }
                    (* FUTURE OPERATORS *)
| "after"
    { main (tokenize NEXT lexbuf :: tokens) lexbuf }
| "always"
    { main (tokenize ALWAYS lexbuf :: tokens) lexbuf }
| ("eventually" | "sometime")
    { main (tokenize EVENTUALLY lexbuf :: tokens) lexbuf }
| "until"
    { main (tokenize UNTIL lexbuf :: tokens) lexbuf }
                    (* PAST OPERATORS *)
| "previous"
    { main (tokenize PREVIOUS lexbuf :: tokens) lexbuf }
| "historically"
    { main (tokenize HISTORICALLY lexbuf :: tokens) lexbuf }
| "once"
    { main (tokenize ONCE lexbuf :: tokens) lexbuf }
| "since"
    { main (tokenize SINCE lexbuf :: tokens) lexbuf }
                    (* F-O QUANTIFIERS + MULTIPLICITIES *)
| "all"
    { main (tokenize ALL lexbuf :: tokens) lexbuf }
| "some"
    { main (tokenize SOME lexbuf :: tokens) lexbuf }
| "one"
    { main (tokenize ONE lexbuf :: tokens) lexbuf }
| "not"
    { main (tokenize NOT lexbuf :: tokens) lexbuf }
| "set"
    { main (tokenize SET lexbuf :: tokens) lexbuf }
| "no"
    { main (tokenize NO lexbuf :: tokens) lexbuf }
| "lone"
    { main (tokenize LONE lexbuf :: tokens) lexbuf }
| "let"
    { main (tokenize LET lexbuf :: tokens) lexbuf }
| "disj"
    { main (tokenize DISJ lexbuf :: tokens) lexbuf }
| "this"
    { main (tokenize THIS lexbuf :: tokens) lexbuf }
| ("iff" | "<=>")
    { main (tokenize IFF lexbuf :: tokens) lexbuf }
| ("implies" | "=>")
    { main (tokenize IMPLIES lexbuf :: tokens) lexbuf }
| "else"
    { main (tokenize ELSE lexbuf :: tokens) lexbuf }
| ("or" | "||")
    { main (tokenize OR lexbuf :: tokens) lexbuf }
| ("and" | "&&")
    { main (tokenize AND lexbuf :: tokens) lexbuf }
| "in"
    { main (tokenize IN lexbuf :: tokens) lexbuf }
| ("not" | "!")
    { main (tokenize NOT lexbuf :: tokens) lexbuf }
| "fact"
    { main (tokenize FACT lexbuf :: tokens) lexbuf }
| "assert"
    { main (tokenize ASSERT lexbuf :: tokens) lexbuf }
| "pred"
    { main (tokenize PRED lexbuf :: tokens) lexbuf }
| "private"                     (* ignored! *)
    { main tokens lexbuf }
| "var"
    { main (tokenize VAR lexbuf :: tokens) lexbuf }
| "fun"
    { main (tokenize FUN lexbuf :: tokens) lexbuf }
| "enum"
    { main (tokenize ENUM lexbuf :: tokens) lexbuf }
| "sig"
    { main (tokenize SIG lexbuf :: tokens) lexbuf }
| "extends"
    { main (tokenize EXTENDS lexbuf :: tokens) lexbuf }
| "abstract"
    { main (tokenize ABSTRACT lexbuf :: tokens) lexbuf }
| "module"
    { main (tokenize MODULE lexbuf :: tokens) lexbuf }
| "open"
    { main (tokenize OPEN lexbuf :: tokens) lexbuf }
| "as"
    { main (tokenize AS lexbuf :: tokens) lexbuf }
| "run"
    { main (tokenize RUN lexbuf :: tokens) lexbuf }
| "for"
    { main (tokenize FOR lexbuf :: tokens) lexbuf }
| "expect"
    { main (tokenize EXPECT lexbuf :: tokens) lexbuf }
| "exactly"
    { main (tokenize EXACTLY lexbuf :: tokens) lexbuf }
| "check"
    { main (tokenize CHECK lexbuf :: tokens) lexbuf }
| "but"
    { main (tokenize BUT lexbuf :: tokens) lexbuf }
| "univ"
    { main (tokenize UNIV lexbuf :: tokens) lexbuf }
| "iden"
    { main (tokenize IDEN lexbuf :: tokens) lexbuf }
| "none"
    { main (tokenize NONE lexbuf :: tokens) lexbuf }
| "_static" as id
    { main (tokenize (IDENT (Ast.Ident.make id)) lexbuf :: tokens) lexbuf }
| identifier as id
    { main (tokenize (IDENT (Ast.Ident.make id)) lexbuf :: tokens) lexbuf }
| "/"
    { main (tokenize SLASH lexbuf :: tokens) lexbuf }
| "="
    { main (tokenize EQ lexbuf :: tokens) lexbuf }
| "("
    { main (tokenize LPAREN lexbuf :: tokens) lexbuf }
| ")"
    { main (tokenize RPAREN lexbuf :: tokens) lexbuf }
| "["
    { main (tokenize LBRACKET lexbuf :: tokens) lexbuf }
| "]"
    { main (tokenize RBRACKET lexbuf :: tokens) lexbuf }
| ","
    { main (tokenize COMMA lexbuf :: tokens) lexbuf }
| ":"
    { main (tokenize COLON lexbuf :: tokens) lexbuf }
| "{"
    {  main (tokenize LBRACE lexbuf :: tokens) lexbuf }
| "}"
    {  main (tokenize RBRACE lexbuf :: tokens) lexbuf }
| "++"
    { main (tokenize OVERRIDE lexbuf :: tokens) lexbuf }
| "+"
    { main (tokenize PLUS lexbuf :: tokens) lexbuf }
| "-"
    { main (tokenize MINUS lexbuf :: tokens) lexbuf }
| ("=<" | "<=")
    { main (tokenize LTE lexbuf :: tokens) lexbuf }
| ">="
    { main (tokenize GTE lexbuf :: tokens) lexbuf }
| "<"
    { main (tokenize LT lexbuf :: tokens) lexbuf }
| ">"
    { main (tokenize GT lexbuf :: tokens) lexbuf }
| "#"
    { main (tokenize CARD lexbuf :: tokens) lexbuf }
| "|"
    { main (tokenize BAR lexbuf :: tokens) lexbuf }
| comment_line (* [^newline]* newline *)
    { line_comment tokens lexbuf }
    (* new_line lexbuf; main tokens lexbuf } *)
(* | comment_line eof *)
(*     { tokenize EOF lexbuf :: tokens } *)
| "/*"
    { comment 1 tokens lexbuf }
    (* { comment (lexeme_start_p lexbuf) tokens lexbuf; *)
    (*   main tokens lexbuf } *)
| eof
    { tokenize EOF lexbuf :: tokens }
| _ as c
    { error lexbuf ("lexical error, unexpected character(s): " 
                    ^ (String.make 1 c)) }
(* and comment openingp tokens = parse *)

and line_comment tokens = parse
| newline
    { new_line lexbuf; main tokens lexbuf }
| eof 
    { tokenize EOF lexbuf :: tokens }
| _
    { line_comment tokens lexbuf }
  

and comment opened tokens = parse
| "/*"
    { comment (opened + 1) tokens lexbuf }
| "*/"
    { let nb = opened - 1 in
      if nb < 1 then main tokens lexbuf
      else comment nb tokens lexbuf }
| newline
    { new_line lexbuf; comment opened tokens lexbuf }
| eof
    { error lexbuf "end of file within unterminated comment" }
| _
    { comment opened tokens lexbuf }


{
(* BEGIN FOOTER *)

let token_to_string = function
  | NUMBER n -> string_of_int n
  | INT -> "INT"
  | IDENT s -> "IDENT(" ^ Ast.Ident.to_string s ^ ")"
  | NICKNAME s -> "NICKNAME(" ^ Ast.Ident.to_string s ^ ")"
  | THIS -> "THIS"
  | AT -> "AT"
  | SOME -> "SOME"
  | RPAREN -> "RPAREN"
  | RBRACKET -> "RBRACKET"
  | RBRACE -> "RBRACE"
  | QSOME -> "QSOME"
  | QONE -> "QONE"
  | QNO -> "QNO"
  | QLONE -> "QLONE"
  | QALL -> "QALL"
  | ONE -> "ONE"
  | NO -> "NO"
  | LPAREN -> "LPAREN"
  | LONE -> "LONE"
  | LET -> "LET"
  | LBRACKET -> "LBRACKET"
  | LBRACE -> "LBRACE"
  | EQ -> "EQ"
  | EOF -> "EOF"
  | DISJ -> "DISJ"
  | COMMA -> "COMMA"
  | COLON -> "COLON"
  | BAR -> "BAR"
  | ALL -> "ALL"
  | OR -> "OR"
  | IMPLIES -> "IMPLIES"
  | IFF -> "IFF"
  | ELSE -> "ELSE"
  | PLUS -> "PLUS"
  | OVERRIDE -> "OVERRIDE"
  | NOT -> "NOT"
  | NEQ -> "NEQ"
  | MINUS -> "MINUS"
  | LTE -> "LTE"
  | LT -> "LT"
  | INTER -> "INTER"
  | IN -> "IN"
  | GTE -> "GTE"
  | GT -> "GT"
  | CARD -> "CARD"
  | AND -> "AND"
  | SET -> "SET"
  | SOME_ARROW_SOME -> "SOME_ARROW_SOME"
  | SOME_ARROW_SET -> "SOME_ARROW_SET"
  | SOME_ARROW_ONE -> "SOME_ARROW_ONE"
  | SOME_ARROW_LONE -> "SOME_ARROW_LONE"
  | SET_ARROW_SOME -> "SET_ARROW_SOME"
  | SET_ARROW_SET -> "SET_ARROW_SET"
  | SET_ARROW_ONE -> "SET_ARROW_ONE"
  | SET_ARROW_LONE -> "SET_ARROW_LONE"
  | ONE_ARROW_SOME -> "ONE_ARROW_SOME"
  | ONE_ARROW_SET -> "ONE_ARROW_SET"
  | ONE_ARROW_ONE -> "ONE_ARROW_ONE"
  | ONE_ARROW_LONE -> "ONE_ARROW_LONE"
  | LONE_ARROW_SOME -> "LONE_ARROW_SOME"
  | LONE_ARROW_SET -> "LONE_ARROW_SET"
  | LONE_ARROW_ONE -> "LONE_ARROW_ONE"
  | LONE_ARROW_LONE -> "LONE_ARROW_LONE"
  | ARROW -> "ARROW"
  | RPROJ -> "RPROJ"
  | LPROJ -> "LPROJ"
  | DOT -> "DOT"
  | TILDE -> "TILDE"
  | STAR -> "STAR"
  | CARET -> "CARET"
  | FACT -> "FACT"
  | ASSERT -> "ASSERT"
  | PRED -> "PRED"
  | PRIVATE -> "PRIVATE"
  | FUN -> "FUN"
  | ENUM -> "ENUM"
  | SIG -> "SIG"
  | EXTENDS -> "EXTENDS"
  | ABSTRACT -> "ABSTRACT"
  | MODULE -> "MODULE"
  | OPEN -> "OPEN"
  | AS -> "AS"
  | RUN -> "RUN"
  | FOR -> "FOR"
  | EXPECT -> "EXPECT"
  | EXACTLY -> "EXACTLY"
  | CHECK -> "CHECK"
  | BUT -> "BUT"
  | SLASH -> "SLASH"
  | MSOME -> "MSOME"
  | MSET -> "MSET"
  | MONE -> "MONE"
  | MLONE -> "MLONE"
  | UNIV -> "UNIV"
  | NONE -> "NONE"
  | IDEN -> "IDEN"
  | PRIME -> "PRIME"
  | VAR -> "VAR"
  | UNTIL -> "UNTIL"
  | NEXT -> "AFTER"
  | EVENTUALLY -> "EVENTUALLY"
  | ALWAYS -> "ALWAYS"
  | SINCE -> "SINCE"
  | PREVIOUS -> "PREVIOUS"
  | ONCE -> "ONCE"
  | HISTORICALLY -> "HISTORICALLY"
    
let print_token t = print_string @@ (token_to_string t ^ " ")

let print_buffer l =
  List.iter (fun (t,_, _) -> print_token t) l;
  print_newline ()

let make_quantifer = function
  | ALL -> QALL
  | SOME -> QSOME
  | LONE -> QLONE
  | NO -> QNO
  | ONE -> QONE
  | _ -> assert false


let transform_arrow x y =
  (* print_endline ("transform_arrow " ^ token_to_string x ^ token_to_string y); *)
  match x, y with
    | SOME, SOME -> SOME_ARROW_SOME 
    | SOME, SET -> SOME_ARROW_SET 
    | SOME, ONE -> SOME_ARROW_ONE 
    | SOME, LONE -> SOME_ARROW_LONE 
    | SET, SOME -> SET_ARROW_SOME 
    | SET, SET -> SET_ARROW_SET 
    | SET, ONE -> SET_ARROW_ONE 
    | SET, LONE -> SET_ARROW_LONE 
    | ONE, SOME -> ONE_ARROW_SOME 
    | ONE, SET -> ONE_ARROW_SET 
    | ONE, ONE -> ONE_ARROW_ONE 
    | ONE, LONE -> ONE_ARROW_LONE 
    | LONE, SOME -> LONE_ARROW_SOME 
    | LONE, SET -> LONE_ARROW_SET 
    | LONE, ONE -> LONE_ARROW_ONE 
    | LONE, LONE -> LONE_ARROW_LONE
    | _ -> assert false

let make_multiplicity = function
  | SOME -> MSOME
  | LONE -> MLONE
  | ONE -> MONE
  | SET -> MSET
  | _ -> assert false

let change_to_multiplicity toks =
  let rec change met_par acc toks = match toks with
    | ((DISJ, _, _) as disj) :: tl when not met_par ->
        change met_par (disj :: acc)  tl
    | ((LPAREN, _, _) as lpar) :: tl ->
        change true (lpar :: acc) tl
    | ((SOME | SET | ONE | LONE as m), m_start, m_end) :: tl ->
        Some (List.rev acc @ (make_multiplicity m, m_start, m_end) :: tl)
    | _ -> None
  in change false [] toks

let rec lexer_hack tokens = match tokens with
  (* handling the special generated fact "_static" *)
  | ((FACT, _, _) as xtriple)
    :: ((IDENT id, _, _) as id_triple)
    :: toks
    when Ast_ident.(compare id _static_as_id) = 0 ->
      xtriple :: id_triple :: lexer_hack toks
                                
  | (IDENT id, _, _)
    :: toks 
    when Ast_ident.(compare id _static_as_id) = 0 -> 
      failwith "lexical error, unexpected string: _static"
                                
  (* changing the token for the nickname of a command,
     avoids a S/R conflict *)
  | (IDENT id, id_start, id_end)
    :: ((COLON, _, _) as colon)
    :: (((RUN | CHECK), _, _) as roc)
    :: toks ->
      (NICKNAME id, id_start, id_end) :: lexer_hack (colon :: roc :: toks)

  (* rewriting builtin predicates and functions *)
  | (PRED, builtin_start, _)
    :: (SLASH, _, _)
    :: ((IDENT id), _, builtin_end)
    :: toks
    when Ast.Ident.to_string id = "totalOrder" ->
      lexer_hack @@
      (IDENT (Ast.Ident.make "pred/totalOrder"), builtin_start, builtin_end)
      :: toks

  (* | (FUN, builtin_start, _) *)
  (*   :: (SLASH, _, _) *)
  (*   :: ((IDENT id), _, builtin_end) *)
  (*   :: toks *)
  (*   when List.mem (Ast_ident.to_string id) *)
  (*         ["add"; "sub"; "mul"; "div"; "rem"; "min"; "max"; "next"] -> *)
  (*   lexer_hack @@ *)
  (*   (make_builtin (Ast_ident.to_string id), builtin_start, builtin_end) :: toks *)

  (* parsing Alloy's 'next' as an identifier if preceded by a slash  *)
   (* | ((SLASH, _, _) as slash)  *)
   (*   :: (NEXT, next_start, next_end)  *)
   (*   :: toks ->  *)
   (*     lexer_hack @@  *)
   (*    slash  *)
   (*   :: (IDENT (Ast.Ident.make "next"), next_start, next_end)  *)
   (*   ::  toks  *)

  (* rewriting arrows with or without multiplicities as single tokens  *)
  | ((SOME | SET | ONE | LONE as x), x_start, _)
    :: (ARROW, _, _)
    :: ((SOME | SET | ONE | LONE as y), _, y_end)
    :: toks ->
      lexer_hack @@ (transform_arrow x y, x_start, y_end) :: toks

  | ((_, _, _) as xtriple)
    :: (ARROW, a_start, _) 
    :: ((SOME | SET | ONE | LONE as y), _, y_end) 
    :: toks ->
      xtriple :: (lexer_hack @@ (transform_arrow SET y, a_start, y_end) :: toks)

  | ((SOME | SET | ONE | LONE as x), x_start, _) 
    :: (ARROW, _, a_end)
    :: ((_, _, _) as ytriple)
    :: toks ->
      (transform_arrow x SET, x_start, a_end) 
      :: (lexer_hack @@ ytriple :: toks)

  | ((_, _, _) as xtriple) 
    :: (ARROW, a_start, a_end) 
    :: ((_, _, _) as ytriple)
    :: toks ->
      xtriple :: (SET_ARROW_SET, a_start, a_end)
      :: (lexer_hack @@  ytriple :: toks)

  (* rewriting multiplicities preceding (what is expected to be) 
     single column relations *)
  | (((COLON | IN), _, _) as xtriple)
    :: toks ->
      begin
        match change_to_multiplicity toks with
          | None -> xtriple :: lexer_hack toks
          | Some modified_list -> xtriple :: lexer_hack modified_list
      end

  | ((ALL | SOME | ONE | LONE | NO as q), q_start, q_end) 
    :: ((DISJ, _, _) as disj_triple)
    :: toks ->
      (make_quantifer q, q_start, q_end) 
      :: lexer_hack (disj_triple :: toks)

  | ((ALL | SOME | ONE | LONE | NO as q), q_start, q_end) 
    :: xtriple 
    :: (((COLON | COMMA), _, _) as sep_triple)
    :: toks ->
      (make_quantifer q, q_start, q_end)
      :: lexer_hack (xtriple :: sep_triple ::  toks)
                                
  | hd :: tl -> hd :: lexer_hack tl
  | [] -> []


let token_buffer = ref [];;      (* token list ref *)

let last_seen = ref None
    
let init infile lexbuf =
  let open Faulty in
  try
    good (token_buffer :=
            main [] lexbuf
            |> List.rev
            (* |> tap (ifthen !Cfg.debug print_buffer) *)
            |> lexer_hack
            (* |> tap (ifthen !Cfg.debug print_buffer) *)
         )
  with Lexing_error msg ->
    fail `ELexing (lazy
                    ((fun (lazy s) -> Printf.sprintf "%s: %s" infile s) msg))

let next () = match !token_buffer with
  | [] -> assert false          (* contains at least EOF *)
  | [ tok ] -> tok
  | tok :: toks ->
      begin
        last_seen := Some tok;
        token_buffer := toks;
        tok
      end

let last_token () =
  !last_seen

(* END FOOTER *)
}
