(*******************************************************************************
 * Electrum Analyzer 
 * Copyright (C) 2014-2015 Onera
 * Authors: 
 *   Julien Brunel <julien DOT brunel AT onera DOT fr>
 *   David Chemouil <david DOT chemouil AT onera DOT fr>
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
open K2
open PPrint

let tabsize = 2
let braces = PPrint.(enclose (lbrace ^^ space) (space ^^ rbrace))

let colon = string "∈"
let lte2 = string "≤"
let lt2 = string "<"
let gte2 = string "≥"
let gt2 = string ">"
let neq2 = string "≠"
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

let document_of_pred p = string p.pred_name

let document_of_int_op2 intop = match intop with
  | Add2 -> plus
  | Sub2 -> minus

let document_of_comp_int2 compint = match compint with
  | Lte2 -> lte2
  | Lt2 -> lt2
  | Gte2 -> gte2
  | Gt2 -> gt2
  | Eq2 -> equals
  | Neq2 -> neq2


let document_of_name_list nlist =
  separate_map comma string nlist


(* let rec document_of_transclosure { v1; v2; prop } = *)
(*   flow space [ *)
(*     tr ^^ underscore; *)
(*     braces (string v1 ^^ comma ^/^ string v2); *)
(*     document_of_prop2 prop *)
(*   ] *)

let rec document_of_term2 term = match term with   
  | TConst i -> string (string_of_int i)  
  | TBin (iop2, t1, t2) ->
      (* flow space [ *)
      (*   document_of_term2 t1; *)
      (*   document_of_int_op2 iop2; *)
      (*   document_of_term2 t2 *)
      (* ] |> parens *)
      
      infix tabsize 1
        (document_of_int_op2 iop2) (document_of_term2 t1) (document_of_term2 t2)
      |> parens
  | TMult (i, term) ->
      flow space [
        string (string_of_int i);
        star;
        document_of_term2 term
      ] |> parens
  | TCard (nlist, p, prof) ->
     flow comma
          [(flow_map space 
              string 
              nlist
           );
           document_of_prop2 p;
          ]
     |> braces
     |> precede sharp

and document_of_prop2_binop p1 p2 op =
  parens @@ infix tabsize 1 op (document_of_prop2 p1) (document_of_prop2 p2)

and document_of_prop2_unop p op =
  op ^//^ parens @@ document_of_prop2 p

and document_of_quant quant x s prop =
  let pref = flow space [
        quant;
        string x;
        colon;
        string s
      ]
  in
  prefix tabsize 1 pref (document_of_prop2 prop |> brackets)
    
and document_of_prop2 prop = match prop with
  | True2 -> s_true
  | False2 -> s_false
  | Equal2 (n1 , n2) ->
      flow space [ string n1; equals ;string n2 ]
  | Comp2 (compint , t1 , t2) ->
      flow space [
        document_of_term2 t1; 
				document_of_comp_int2 compint;
			  document_of_term2 t2
      ]
  | ConstPred2 (p , nlist) ->
      (string "CONST")^^ 
      document_of_pred p
      ^^ surround_separate_map 2 0
           empty lparen (comma ^^ space) rparen string nlist
  | VarPred2 (p , nlist) -> 
     (string "VAR") ^^
      document_of_pred p
      ^^ surround_separate_map 2 0
           empty lparen (comma ^^ space) rparen string nlist

  (* propositional connectives *)
  | Not2 prop -> document_of_prop2_unop prop s_not
  | And2 (p1 , p2) -> document_of_prop2_binop p1 p2 s_and
  | Or2 (p1 , p2) -> document_of_prop2_binop p1 p2 s_or
  | Impl2  (p1, p2) -> document_of_prop2_binop p1 p2 s_implies
  | Iff2  (p1, p2) -> document_of_prop2_binop p1 p2 s_iff
  (* quantifiers *)
  | Forall2 (x , s , prop) -> document_of_quant s_all x s prop
  | Exists2  (x , s , prop) -> document_of_quant s_some x s prop

  (* temporal connectives *)
  | Next2  prop -> document_of_prop2_unop prop s_x
  | Always2  prop -> document_of_prop2_unop prop s_g
  | Eventually2 prop -> document_of_prop2_unop prop s_f
  | Until2  (p1, p2) -> document_of_prop2_binop p1 p2 s_u
  | Release2 (p1, p2) -> document_of_prop2_binop p1 p2 s_r
  | Previous2 prop -> document_of_prop2_unop prop s_p
  | Hist2  prop -> document_of_prop2_unop prop s_h
  | Once2 prop -> document_of_prop2_unop prop s_o
  | Since2  (p1, p2) -> document_of_prop2_binop p1 p2 s_s

let k2prop_to_string p2=Util.PPrintX.to_string @@ document_of_prop2 p2
