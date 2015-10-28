(*****************************************************************************
 * Time-stamp: <2015-01-29 CET 11:15:47 David Chemouil>
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
 ****************************************************************************)

(*****************************************************************************
 * ast_file.ml -- abstract syntax tree for Electrum files
 ****************************************************************************)

open Batteries
open Ast_expr
open Ast_par
open Ast_ctrl

(* module name and formal parameters *)
type module_decl = Ast_qname.t * Ast_qname.t list 

let make_module_decl ~module_name ~params = (module_name, params)

(* opened module, effective parameters, punning ('as ...') *)
type import = Ast_qname.t * Ast_qname.t list * Ast_ident.t option

let make_import ~module_name ~params ~pun =
  (module_name, params, pun)

type par_cmd =
  | Par of paragraph
  | Cmd of cmd

type file = module_decl option * import list * par_cmd list

type imp_par = Imp of import | Parag of Ast_par.paragraph

type file_sorted = imp_par list
