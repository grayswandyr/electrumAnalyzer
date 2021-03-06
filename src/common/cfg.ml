(*******************************************************************************
 * Time-stamp: <2015-10-23 CEST 15:14:02 David Chemouil>
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

(*****************************************************************************
 * config.ml - for global data in the program
 ****************************************************************************)

open Batteries
open Faulty


let debug = ref false

let print_debug s = if !debug then Printf.eprintf "DEBUG: %s%!" s

let program_name = "electrumAnalyzer" 

let app_name = "Electrum Analyzer" 

let extension= ".als"

let alloyfolder= ref "./"

