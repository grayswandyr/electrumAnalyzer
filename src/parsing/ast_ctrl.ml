(*****************************************************************************
 * Time-stamp: <2015-01-28 CET 11:07:58 David Chemouil>
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
 * ast_ctrl.ml -- abstract syntax tree for Electrum commands 
 ****************************************************************************)

open Batteries
open Ast_expr

type cmd_type = Run | Check

type typescope = bool * int * Ast_qname.t (* bool = true => 'exactly' *)

let make_typescope ~exactly ~num ~sig_name =
  verify_arg (num >= 0)
    ("negative scope for signature " ^ Ast_qname.to_string sig_name);
  (exactly, num, sig_name)

type scope =
  | ForBut of int * typescope list      (* for number but typescopes... *)
  | ForTypes of typescope list          (* for typescopes... *)

let make_scope_for_but ~num ~typescopes =
  verify_arg (num >= 0) "negative scope in 'for ... but ...' command";
  ForBut (num, typescopes)

let make_scope_for_types ~typescopes = ForTypes typescopes


type cmd = 
  | NamedCmd of Ast_qname.t * cmd_type * scope option * Ast_ident.t option
  | BlockCmd of block * cmd_type * scope option * Ast_ident.t option

let make_named_cmd ~qname ~cmd ~scope ~nick =
  NamedCmd (qname, cmd, scope, nick)

let make_block_cmd ~block ~cmd ~scope ~nick =
  BlockCmd (block, cmd, scope, nick)
