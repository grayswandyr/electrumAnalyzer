(*****************************************************************************
 * Time-stamp: <2015-05-26 CEST 11:29:13 David Chemouil>
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
 * location.ml -- locations in Electrum source code
 ****************************************************************************)

open Batteries
open Lexing

type t = {
  begp : Lexing.position;
  endp : Lexing.position
}

let make ~begp ~endp = {
  begp; endp
}

let dummy_loc=make Lexing.dummy_pos Lexing.dummy_pos 

let to_string pos=
  let col1=pos.begp.pos_cnum-pos.begp.pos_bol in
  let col2=pos.endp.pos_cnum-pos.endp.pos_bol in
  "Line "^(string_of_int pos.begp.pos_lnum)
  ^" characters "^(string_of_int col1)
  ^"-"^(string_of_int col2)
