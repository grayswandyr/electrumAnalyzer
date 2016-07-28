(*******************************************************************************
 * Electrum Analyzer 
 * Copyright (C) 2014-2015 Onera
 * Authors: 
 *   Julien Brunel 
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

open Batteries
open K1
open PPrint

let tabsize = 2
let braces = PPrint.(enclose (lbrace ^^ space) (space ^^ rbrace))

let comma_sp = comma ^^ space
let colon = string "∈"
let lte = string "≤"
let lt = string "<"
let gte = string "≥"
let gt = string ">"
let neq = string "≠"
let tr = string "TR_"

let s_in = string "in"
let s_true = string "⊤"
let s_false = string "⊥"
let s_all = string "∀"
let s_some = string "∃"
let s_not = string "¬"
let s_and = string "∧"
let s_or = string "∨"
let s_implies = string "⇒"
let s_iff = string "⇔"
let s_x = string "X"
let s_f = string "F"
let s_g = string "G"
let s_u = string "U"
let s_r = string "R"
let s_p = string "Y"
let s_h = string "H"
let s_o = string "O"
let s_s = string "S"

let s_if = string "if"
let s_then = string "then"
let s_else = string "else"


let document_of_un_op = function
  | Trans -> caret
  | Prime -> squote
  | Tilde -> tilde

let document_of_bin_op = function
  | Union -> plus
  | Inter -> ampersand
  | Diff -> minus
  | Product -> star
  | Join -> dot

let rec document_of_term { term; profile } =
  document_of_raw_term term

and document_of_bindings bindings =
  separate_map comma_sp
    (fun (x, t) -> string x ^^ colon ^^ space ^^ document_of_term t)
    bindings

and document_of_raw_term = function
  | TConstRel n -> string n
  | TVarRel n  -> string n
  | TSort n | TVar n -> string n
  | TUnop (Prime, t) -> document_of_term t ^^ squote
  | TUnop (op, t) -> document_of_un_op op ^^ document_of_term t
  | TBinop (Join as op, t1, t2)  ->
      parens @@
      document_of_term t1
      ^^ document_of_bin_op op
      ^^ document_of_term t2
  | TBinop (op, t1, t2)  ->
      infix tabsize 1
        (document_of_bin_op op) (document_of_term t1) (document_of_term t2)
      |> parens
  | TIfThenElse (p, t1, t2) ->
      parens @@
      s_if ^^ space ^^ document_of_prop p
      ^/^ s_then ^^ space ^^ document_of_term t1
      ^/^ s_else ^^ space ^^ document_of_term t2
  | TCompr (bindings, p) ->
      infix tabsize 1 bar (document_of_bindings bindings) (document_of_prop p)
      |> braces

and document_of_int_op = function
  | Add  -> plus
  | Sub  -> minus

and document_of_iexpr = function
  | IConst i  -> string @@ string_of_int i
  | IVar n  -> string n
  | IOp (op, e1, e2)  ->
      infix tabsize 1
        (document_of_int_op op) (document_of_iexpr e1) (document_of_iexpr e2)
  | IMult (i, e)  -> 
      infix tabsize 1 star (string @@ string_of_int i) (document_of_iexpr e)
  | ICard t -> sharp ^^ (parens @@ document_of_term t)

and document_of_comp_int = function
  | Lte  -> lte
  | Lt  -> lt
  | Gte  -> gte
  | Gt  -> gt
  | Eq  -> equals
  | Neq -> neq

and document_of_prop_binop p1 p2 op = 
  parens @@ infix tabsize 1 op (document_of_prop p1) (document_of_prop p2)

and document_of_prop_unop p op =
  op ^//^ document_of_prop p

and document_of_quant quant xs t p =
  let pref = flow space [
        quant;
        separate_map comma_sp string xs;
        colon;
        document_of_term t
      ]
  in
  prefix tabsize 1 pref (document_of_prop p |> brackets)

and document_of_prop = function
  | Equal (t1, t2) -> 
      flow space [ document_of_term t1; equals; document_of_term t2 ]
      |> parens
  | In (t1, t2) -> 
      flow space [ document_of_term t1; s_in; document_of_term t2 ]
      |> parens
  | Comp (comp, t1, t2) -> 
      flow space [
        document_of_iexpr t1; 
        document_of_comp_int comp;
        document_of_iexpr t2
      ]
      |> parens
  | True -> s_true
  | False -> s_false
  | Not p -> document_of_prop_unop p s_not
  | And (p1, p2) -> document_of_prop_binop p1 p2 s_and
  | Or (p1, p2) -> document_of_prop_binop p1 p2 s_or
  | Impl (p1, p2) -> document_of_prop_binop p1 p2 s_implies
  | Iff (p1, p2) -> document_of_prop_binop p1 p2 s_iff
  | Next p  -> document_of_prop_unop p s_x
  | Always p  -> document_of_prop_unop p s_g
  | Eventually p  -> document_of_prop_unop p s_f
  | Until (p1, p2) -> document_of_prop_binop p1 p2 s_u
  | Release (p1, p2) -> document_of_prop_binop p1 p2 s_r
  | Previous p -> document_of_prop_unop p s_p
  | Hist p -> document_of_prop_unop p s_h
  | Once p -> document_of_prop_unop p s_o
  | Since (p1, p2) -> document_of_prop_binop p1 p2 s_s
  | Forall (xs, t, p) -> document_of_quant s_all xs t p
  | Exists (xs, t, p) -> document_of_quant s_some xs t p

let string_of_term t = Util.PPrintX.to_string @@ document_of_term t

let string_of_prop t = Util.PPrintX.to_string @@ document_of_prop t

let string_of_bindings bs = Util.PPrintX.to_string @@ document_of_bindings bs

let simple_string_of_term t =
  let r = Str.regexp "\\([^A-Za-z0-9]\\)" in
  Str.global_replace r "_" (string_of_term t)

let format_var_name s =
  let r = Str.regexp "/" in
  Str.global_replace r "_" s
                     
