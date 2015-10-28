(*******************************************************************************
 * Time-stamp: <2015-06-25 CEST 10:32:42 David Chemouil>
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

open Batteries
open Util
open Names
 
let fresh, reset =
  let start = (-1) in
  let count = ref start in
  let f ?(sep = "") base =
    incr count;
    let v = Printf.sprintf "_%s%s%d" base sep !count in
    (*Cfg.print_debug
    @@ Printf.sprintf "Fresh.fresh: new variable %s\n%!" v;*)
    v
  in
  let r () = count := start
  in
  (Names.make % f, r)
    
