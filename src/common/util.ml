(*******************************************************************************
 * Time-stamp: <2015-06-25 CEST 15:00:04 David Chemouil>
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

(*****************************************************************************
 * util.ml - generic additions to Batteries & the standard lib
 ****************************************************************************)

open Batteries

let ifthenelse c t e x = if c then t x else e x

let ifthen c t x = ifthenelse c t ignore x

module PPrintX = struct
  open PPrint
      
  let to_string ?(ribbon=0.95) ?(width=80) doc =
    let buf = Legacy.Buffer.create 100 in
    ToBuffer.pretty ribbon width buf doc;
    Legacy.Buffer.contents buf

  let print ?(ribbon=0.9) ?(width=80) doc =
    ToChannel.pretty ribbon width Legacy.stdout doc

  let eprint ?(ribbon=0.9) ?(width=80) doc =
    ToChannel.pretty ribbon width Legacy.stderr doc
end

module OptionX = struct
  open BatOption
  let map2 ~f op1 op2 = match op1, op2 with
    | Some x, Some y -> Some (f x y)
    | _ -> None
  let map2_default ~f op1 op2 d = match op1, op2 with
    | Some x, Some y -> f x y
    | _ -> d

  let to_string elt_printer l =
    BatIO.to_string (Option.print elt_printer) l
end

module ListX = struct               
  let to_string ?first ?last ?sep elt_printer l =
    BatIO.to_string (List.print ?first ?last ?sep elt_printer) l

  let rec flat_map f l = match l with 
    | [] -> []
    | h::t -> f h @ flat_map f t
end

module StringX = struct
  open String
  let surround left right s =
    concat "" [ left; s; right ]
  let surround_sep left right sep strings =
    concat sep strings |> surround left right
end
