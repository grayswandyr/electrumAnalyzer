(*******************************************************************************
 * Time-stamp: <2015-01-16 CET 16:21:49 David Chemouil>
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

type module_decl = Ast_qname.t * Ast_qname.t list 

val make_module_decl :
  module_name:Ast_qname.t -> params:Ast_qname.t list -> module_decl

type import = Ast_qname.t * Ast_qname.t list * Ast_ident.t option

val make_import :
  module_name:Ast_qname.t -> params:Ast_qname.t list ->
  pun:Ast_ident.t option -> import

type par_cmd = Par of Ast_par.paragraph | Cmd of Ast_ctrl.cmd

type file = module_decl option * import list * par_cmd list

(* commands are not typechecked for now *)
type imp_par = Imp of import | Parag of Ast_par.paragraph

type file_sorted = imp_par list

(* val make_file : *)
(*   mod_decl:module_decl -> imports:import list *)
(*   -> pocs:par_cmd list -> file *)
