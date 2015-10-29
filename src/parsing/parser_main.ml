(*******************************************************************************
 * Time-stamp: <2015-06-12 CEST 14:15:15 David Chemouil>
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

(*****************************************************************************
 * parser_main.ml - functions for calling the parser
 ****************************************************************************)

open Batteries
open Faulty

let syntax_error file tok t_start t_end = 
  let open Scanner in
  let line_start, col_start = line_column t_start in
  let line_end, col_end = line_column t_end in
  let lines = File.lines_of file
              |> Enum.skip (line_start - 1)
              |> Enum.take 1
              |> Enum.get |? "" in
  let msg = lazy (Printf.sprintf
                    "%s: syntax error at line %d, column %d - \
                     line %d, column %d on terminal ``%s'':\n%s"
                    file line_start col_start line_end col_end
                    (token_to_string tok) lines) in
  fail `ESyntax msg

let parse_scan file lexer =
  try
    good (MenhirLib.Convert.Simplified.traditional2revised Parser.file lexer)
  with Parser.Error -> 
  match Scanner.last_token () with
    | None -> assert false    (* there's at least EOF *)
    | Some (t, t_start, t_end) -> syntax_error file t t_start t_end

let parse infile =
  let open Faulty.Monad in
  let inchan = File.open_in infile in
  let lexbuf = Lexing.from_channel inchan in
  let ast =
    Scanner.init infile lexbuf >>= fun () -> (* lexing, then lexer hack *)
    parse_scan infile Scanner.next >>= (good % Ast.Alpha.rename) >>= (good % Ast.Hull.add_hull )
  in
  IO.close_in inchan;
  ast
