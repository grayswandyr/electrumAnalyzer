(*****************************************************************************
 * Time-stamp: <2015-07-23 CEST 14:29:08 David Chemouil>
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
 * ast_qname.mli -- managing qualified names 
 ****************************************************************************)

type t

val make : this:bool -> path:Ast_ident.t list -> name:Ast_ident.t -> t

val to_ident : t -> Ast_ident.t

val to_string : t -> string

val to_document : t -> PPrint.document

val add_pref : Ast_ident.t option -> t -> t

val local : Ast_ident.t -> t

val update : t -> Ast_ident.t -> t
