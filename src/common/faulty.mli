(*******************************************************************************
 * Time-stamp: <2015-05-12 CEST 09:58:09 David Chemouil>
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
 * faulty.mli - for functions that may fail (based upon the Result monad)
 ****************************************************************************)

(* a computation that may fail is a particular sort of result
   where the Bad case contains and error as defined above *)
type ('ok, 'err) faulty = ('ok, 'err * string Lazy.t) Batteries.Result.t

val fail : ([>  ] as 'err) -> string Lazy.t -> ('ok, 'err) faulty

val good : 'a -> ('a, _) faulty

module Monad : sig
  val bind :('ok1, ([>  ] as 'err)) faulty -> ('ok1 -> ('ok2, 'err) faulty)
    -> ('ok2, 'err) faulty
  val ( >>= ) :('ok1, ([>  ] as 'err)) faulty -> ('ok1 -> ('ok2, 'err) faulty)
    -> ('ok2, 'err) faulty
  val return : 'a -> ('a, _) faulty

  val lift1 : ('a -> 'b) -> ('a, 'err) faulty -> ('b, 'err) faulty
  val lift2 : ('a -> 'b -> 'c) -> ('a, 'err) faulty -> ('b, 'err) faulty -> ('c, 'err) faulty
end

module Infix : sig
  val ( >>= ) :
    ('ok1, ([>  ] as 'err)) faulty
    -> ('ok1 -> ('ok2, 'err) faulty)
    -> ('ok2, 'err) faulty

end

val handle :
  handle:(([>  ] as 'err) -> string -> 'a)
  -> f:('ok -> 'a)
  -> ('ok, 'err) faulty
  -> 'a
