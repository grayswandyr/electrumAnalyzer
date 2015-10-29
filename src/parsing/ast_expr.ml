(*****************************************************************************
 * Time-stamp: <2015-10-16 CEST 10:31:55 David Chemouil>
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
 * ast_expr.ml -- abstract syntax tree for Electrum expressions
 ****************************************************************************)

(* remove warning for duplicate field names in records *)
[@@@warning "-30"]

open Batteries


(* In Alloy, keywords such as 'some', 'lone', etc. may be employed in
   various situations. Instead of creating different constructors for
   these depending on the context of their use, we define them here as
   polymorphic variants. *)
type some_lone_one = [ `Some | `One | `Lone ]

(* for formulas of the shape 'some E' *)
type qualifier = [ some_lone_one | `No ] 

(* for multiplicities in expressions of the shape '... [in/:] some E' *)
type multiplicity = [ some_lone_one | `Set ]

type rel_quantifier = [ qualifier | multiplicity ]

type quantifier = [ qualifier | `All ]

type enumerators = [ rel_quantifier | quantifier ]

let enumerators_to_string : enumerators -> string = function
  | `Some -> "some"
  | `One -> "one"
  | `Lone -> "lone"
  | `No -> "no"
  | `Set -> "set"
  | `All -> "all"

type constant =
  | CNum : int -> constant
  | CNone : constant
  | CIden : constant
  | CUniv : constant
  | CInt : constant

let constant_to_string = function
  | CNum n -> string_of_int n
  | CNone -> "none"
  | CIden -> "iden"
  | CUniv -> "univ"
  | CInt -> "Int"


type comparison =
  | CEq
  | CNeq                                
  | CIn
  | CNotIn                              
  | CLt
  | CGt
  | CLte
  | CGte

let comparison_to_string = function
  | CEq -> "="
  | CNeq -> "!="                            
  | CIn -> "in"
  | CNotIn -> "not in"                            
  | CLt -> "<"
  | CGt -> ">"
  | CLte -> "=<"
  | CGte -> ">="

let negate = function
  | CEq -> CNeq
  | CNeq -> CEq
  | CIn -> CNotIn
  | CNotIn -> CIn
  | CLt -> CGte
  | CGt -> CLte
  | CLte -> CGt
  | CGte -> CLt

(* unary operators *)
type unary =
  | UMinus 
  | UNot 
  | UQual of qualifier
  | UMult of multiplicity
  | UCard 
  | UTilde 
  | UStar 
  | UHat 
  | UPrime
  | UAlways
  | UEventually
  | UNext
  | UPrevious
  | UOnce
  | UHist

let unary_to_string = function
  | UMinus -> "-"
  | UNot -> "not"
  | UQual q -> enumerators_to_string (q :> enumerators)
  | UMult q -> enumerators_to_string (q :> enumerators)
  | UCard -> "#"
  | UTilde -> "~"
  | UStar -> "*"
  | UHat -> "^"
  | UPrime -> "'"
  | UAlways -> "always"
  | UEventually -> "sometime"
  | UNext -> "next"
  | UPrevious -> "previous"
  | UOnce -> "once"
  | UHist -> "historically"

(* binary operators *)
type binary =
  (* logic *)
  | BOr 
  | BAnd 
  | BImp 
  | BIff
  | BUntil
  | BSince
  (* set & relational operators *)
  | BUnion 
  | BInter 
  | BMinus 
  | BOver 
  | BLProj 
  | BRProj 
  | BDot 

let binary_to_string = function
  | BOr -> "or"
  | BAnd -> "and"
  | BImp -> "implies"
  | BIff -> "iff"
  | BUntil -> "until"
  | BSince -> "since"
  | BUnion -> "+"
  | BInter -> "&"
  | BMinus -> "-"
  | BOver -> "++"
  | BLProj -> "<:"
  | BRProj -> ":>"
  | BDot -> "."

(* annotated expr *)
type expr = {
  expr : prim_expr;
  loc : Location.t;
  mutable typ : Types.bound_type option
}

and prim_expr =
  (* this *)
  | EThis
  (* constants *)
  | EConst of constant 
  (* let (local definition) *)
  | ELet of def list * block 
  (* quantified formulas *)
  | EQuant of quantifier * decl list * block 
  (* unary operator preceding an expression *)
  | EUnary of unary * expr 
  (* binary operator *)
  | EBinary of expr * binary * expr 
  (* cartesian product with multiplicities à la UML *)
  | ECart of expr * multiplicity * multiplicity * expr 
  (* comparison of expressions *)
  | EComp of expr * comparison * expr 
  (* ... implies ... else ... (no else == "else true") *)
  | EIte of expr * expr * expr 
  (* function/predicate application *)
  | EApp of  expr * expr list 
  (* ident prefixed by '@': ident shouldn't be dereferenced *)
  | EAtName of Ast_ident.t
  (* qualified name *)
  | EQualName of Ast_qname.t
  (* block = possibly-empty list of expressions  *)
  | EBlock of block 
  (* relation defined by comprehension *)
  | ECompr of decl list * block 

(* a block, i.e. a list of expressions *)
and block = expr list

(* rule 'decl' *)
and decl = {
  is_variable : bool;
  is_disjoint_variables : bool;
  names : Ast_ident.t list;
  range : expr;
  is_disjoint_ranges : bool
}

(* local definition, called let-declaration in the Alloy grammar *)
and def = {
  name : Ast_ident.t;
  expr : expr
}

let make_decl ~is_variable ~is_disjoint_variables ~names
      ~range ~is_disjoint_ranges = {
  is_variable;
  is_disjoint_variables;
  names;
  range;
  is_disjoint_ranges;
}

let make_def ~name ~expr =
  { name; expr }

let make_expr ?(typ = None) loc expr : expr = {
  loc; expr; typ
}
