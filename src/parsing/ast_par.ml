(*****************************************************************************
 * Time-stamp: <2015-05-13 CEST 16:12:45 David Chemouil>
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
 ****************************************************************************)

(*****************************************************************************
 * ast_par.ml -- abstract syntax tree for Electrum "paragraphs"
 ****************************************************************************)

open Batteries

(* remove warning for duplicate field names in records *)
[@@@warning "-30"]

open Ast_expr



type sig_ext =
  (* extending one signature *)
  | Extends of Ast_qname.t
  (* inclusion in at least one signature *)
  | In of Ast_qname.t list

type signature = {
  is_variable : bool;
  is_abstract : bool;
  mult : some_lone_one option;
  names : Ast_ident.t list; (* possibly many signatures defined simultaneously *)
  extends : sig_ext option;
  fields : decl list;
  fact : block option
}

let make_signature
      ~is_variable ~is_abstract ~mult ~names ~extends ~fields ~fact =
  { is_variable; is_abstract; mult; names; extends; fields; fact } 

type enum = {
  name : Ast_ident.t;
  cases : Ast_ident.t list;                      (* must be non empty *)
}

let make_enum ~name ~cases =
  verify_arg (cases <> []) (Ast_ident.to_string name
                            ^ ": enumeration with an empty set of cases");
  { name ; cases }

type fact =  {
  name : Ast_ident.t option;
  body : block
}

let make_fact ~name ~body =
  { name; body }

type pred = {
  name : Ast_ident.t;
  params : decl list;
  body : block
}

let make_pred ~name ~params ~body =
  { name; params; body }

type func = {
  name : Ast_ident.t;
  params : decl list;
  returns : expr;
  body : expr
}

let make_func ~name ~params ~returns ~body =
  { name; params; returns; body }

type assertion = {
  name : Ast_ident.t option;
  body : block
}

let make_assertion ~name ~body =
  { name; body }

(* declarations (paragraphs in the Alloy grammar) 
   (does not contain commands, contrary to Alloy, to decouple these concerns)
*)
type paragraph =
  | Sig of signature
  | Enum of enum
  | Fact of fact
  | Pred of pred
  | Fun of func
  | Assert of assertion

