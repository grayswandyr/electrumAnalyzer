(*******************************************************************************
 * Time-stamp: <2015-05-12 CEST 09:58:00 David Chemouil>
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
 * faulty.ml - for functions that may fail (based upon the Result monad)
 ****************************************************************************)

open Batteries

type ('ok, 'err) faulty = ('ok, 'err * string Lazy.t) result 

let fail err msg = Bad (err, msg)

let good x = Ok x

module Monad = struct
  let bind m k = match m with
    | Ok x -> k x
    | Bad _ as e -> e
  let return = good
  let ( >>= ) = bind
  let lift1 f m= match m with
    | Ok x -> return (f x)
    | Bad (err, lazy msg) -> Bad (err, lazy msg) 
  let lift2 f m n=match m with
    | Ok x -> (match n with
          | Ok y -> return (f x y)
          | Bad (err, lazy msg) -> Bad (err, lazy msg))
    | Bad (err, lazy msg) -> Bad (err, lazy msg) 
end

module Infix = struct
  let ( >>= ) m k = match m with
    | Ok x -> k x
    | Bad _ as e -> e
end

let handle ~handle ~f x = match x with
  | Ok res -> f res
  | Bad (err, lazy msg) -> handle err msg
