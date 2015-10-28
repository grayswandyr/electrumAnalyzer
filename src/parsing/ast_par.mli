(*******************************************************************************
 * Time-stamp: <2015-03-05 CET 14:02:19 David Chemouil>
 * 
 * Electrum Analyzer 
 * Copyright (C) 2014-2015 Onera
 * Authors: 
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

type sig_ext = Extends of Ast_qname.t | In of Ast_qname.t list
                   
type signature = {
  is_variable : bool;
  is_abstract : bool;
  mult : Ast_expr.some_lone_one option;
  names : Ast_ident.t list;
  extends : sig_ext option;
  fields : Ast_expr.decl list;
  fact : Ast_expr.block option;
}

val make_signature :
  is_variable:bool ->
  is_abstract:bool ->
  mult:Ast_expr.some_lone_one option ->
  names:Ast_ident.t list ->
  extends:sig_ext option ->
  fields:Ast_expr.decl list ->
  fact:Ast_expr.block option -> signature
  
type enum = { name : Ast_ident.t; cases : Ast_ident.t list; }
            
val make_enum : name:Ast_ident.t -> cases:Ast_ident.t list -> enum
  
type fact = {
  name : Ast_ident.t option;
  body : Ast_expr.block;
}
              
val make_fact :
  name:Ast_ident.t option -> body:Ast_expr.block -> fact
                                       
type pred = {
  name : Ast_ident.t;
  params : Ast_expr.decl list;
  body : Ast_expr.block;
}

val make_pred :
  name:Ast_ident.t ->
  params:Ast_expr.decl list ->
  body:Ast_expr.block -> pred
  
type func = {
  name : Ast_ident.t;
  params : Ast_expr.decl list;
  returns : Ast_expr.expr;
  body : Ast_expr.expr;
}

val make_func :
  name:Ast_ident.t ->
  params:Ast_expr.decl list ->
  returns:Ast_expr.expr ->
  body:Ast_expr.expr -> func
  
type assertion = {
  name : Ast_ident.t option;
  body : Ast_expr.block;
}

val make_assertion :
  name:Ast_ident.t option -> body:Ast_expr.block -> assertion
  
type paragraph =
    Sig of signature
  | Enum of enum
  | Fact of fact
  | Pred of pred
  | Fun of func
  | Assert of assertion
