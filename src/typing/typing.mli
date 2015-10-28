(*****************************************************************************
 * Time-stamp: <2015-04-27 CEST 11:35:00 David Chemouil>
 *
 * Electrum Analyzer 
 * Copyright (C) 2014-2015 Onera
 * Authors: 
 *   Denis Kuperberg <denis DOT kuperberg AT onera DOT fr>
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
typing.mli -- computes the bound type of Electrum expressions


Specification:

An environment envir_sig contains fields:
	*env_map mapping names to types, for variables
	*sign_ord: mapping each signature name to the set of bigger signatures
	*pred_map: mapping each predicate name to a tuple of types, describing its arity

compute_bt takes an expression and an environment, and computes the type. It updates the field typ of the expression with the result.

process_root takes a file and types everything in it, including external files called by it, then returns the computed environment.
It labels each expression of the AST with the computed type, for further use.

 ****************************************************************************)
 
 

 
open Types

type envir_sig = {
	env_map:envir;
	sign_ord:sig_order;
	cursig:bound_type option;
	predmap: envirlist;
	predicates: Ast.Par.pred map;
	facts_typed: bool;
	sig_list: (Ast_qname.t list * Ast_par.signature) list;
	funclist: (Ast_qname.t * Ast_par.func) list;
	factlist: Ast_par.fact list;
	cmdlist: Ast_ctrl.cmd list;
	assertlist: Ast_par.assertion list;
	last_try: bool;
	}

val rep_expr: Ast_qname.t -> Ast_expr.prim_expr -> Ast_expr.expr -> Ast_expr.expr

val empty_envir: envir_sig

val envirsig_to_string: envir_sig -> string

val totpred: Ast_expr.expr -> Ast_expr.expr -> Ast_expr.expr -> Ast_expr.expr -> Ast_expr.expr

val compute_bt : Ast_expr.expr -> envir_sig -> (bound_type, [ `ETyping ] ) Faulty.faulty

val process_root : Ast_file.file -> (envir_sig, [ `ETyping ] ) Faulty.faulty
