(*****************************************************************************
 * Time-stamp: <2015-07-23 CEST 14:30:11 David Chemouil>
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
 * ast_qname.ml -- managing qualified names 
 ****************************************************************************)

open Batteries
  
type t = {
  this : bool;
  path : Ast_ident.t list;
  name : Ast_ident.t;
}

let make ~this ~path ~name = {
  this; path; name
}

let to_ident qn =
  qn.name

let to_string { this; path; name } = 
  (if this then Electrum.Kwd.this_ ^ "/" else "")
  ^ List.fold_left (fun acc id -> acc ^ Ast_ident.to_string id ^ "/") "" path
  ^ Ast_ident.to_string name

let to_document qn = PPrint.string @@ to_string qn

let add_pref (this_pref, path_pref, ident_pref) (this, path, name) =
  if Ast_ident.to_string ident_pref = "" then
    (this_pref , path_pref @ path, name)
  else
    (this_pref, path_pref @ [ ident_pref ] @ path, name)

let add_pref pref qn =
  if Ast_ident.to_string pref.name = "" then
    make pref.this (pref.path @ qn.path) qn.name
  else
    make pref.this (pref.path @ [ pref.name ] @ qn.path) qn.name

(*function for local qname from ident*)
let local idt=make false [] idt  

let of_simple_string s =
  make false [] (Ast_ident.make s)

(* returns the same whole qualified name, except that the name itself is update
   to a new one *)
let update qn newn =
  { qn with name = newn }
