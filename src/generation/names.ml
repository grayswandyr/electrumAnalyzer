(*******************************************************************************
 * Time-stamp: <2015-10-23 CEST 10:38:17 David Chemouil>
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

(* names.ml - names handling common to several phases of compilation *)

open Batteries

type name = string

let univ = "univ"

let int = "int"

let ident = "iden"

let empty = "none"

let make s =
  if (* s = univ || *) s = int then
    failwith (Printf.sprintf "%s: reserved name for Names sorts" s)
  else
    s

let compare = String.compare
 
