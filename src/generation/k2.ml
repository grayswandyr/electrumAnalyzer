(*******************************************************************************
 * Time-stamp: <2015-10-29 CET 09:40:31 David Chemouil>
 * 
 * Electrum Analyzer 
 * Copyright (C) 2014-2015 Onera, (C) 2015 IRIT
 * Authors: 
 *   Denis Kuperberg <denis DOT kuperberg AT gmail DOT com>
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
open Names
  
module Pred : sig
  type pred = private { 
    pred_name : name; 
    pred_prof : Profile.t
  }
  val make : name -> Profile.t -> pred
  (*val pred_of_rel : K1.rel -> pred*)
end
= struct
  type pred = { 
    pred_name : name; 
    pred_prof : Profile.t
  }
  let make pred_name pred_prof = { pred_name; pred_prof }
  (*let pred_of_rel { K1.rel_name; K1.rel_prof } =
    { pred_name = rel_name; 
      pred_prof = rel_prof }*)
end
include Pred

type int_op2 =
  | Add2
  | Sub2
    
type comp_int2 =
  | Lte2 
  | Lt2
  | Gte2
  | Gt2
  | Eq2 
  | Neq2

type term2 =
  | TConst of int 
  | TBin of int_op2 * term2 * term2 
  | TMult of int * term2 
  (*{x in t | x in profile(phi) } *)
  (* In order to count the number of instances of a K1 term t, we use
  a K2 formula p expressing the membership of a list xs of fresh variables in
  the K1 term t.  (# t) in K1 is translated into the K2 term TCardrd (xs, p,
  prof), where prof is the profile of t. During the transformation
  into LTL, this formula will be instantiated assigning xs to each possible 
  value following prof. 
  *) 
  | TCard of (name list) * prop2 * Profile.t

and prop2 =
  (* building propositions *)
  | True2
  | False2
  | Equal2 of name * name
  | Comp2 of comp_int2 * term2 * term2  
  | ConstPred2 of pred * name list    (* check length and typing! *)
  | VarPred2 of pred * name list      (* check length and typing! *)
  (* propositional connectives *)
  | Not2 of prop2
  | And2 of prop2 * prop2
  | Or2 of prop2 * prop2
  | Impl2 of prop2 * prop2
  | Iff2 of prop2 * prop2
  (* quantifiers *)
  | Forall2 of name * name * prop2
  | Exists2 of name * name * prop2

  (* temporal connectives of future *)
  | Next2 of prop2
  | Always2 of prop2
  | Eventually2 of prop2
  | Until2 of prop2 * prop2
  | Release2 of prop2 * prop2

  (* temporal connectives of past *)
  | Previous2 of prop2 (* Next2^-1 *)
  | Hist2 of prop2 (* Always2^-1 *)
  | Once2 of prop2 (* Eventually2^-1 *)
  | Since2 of prop2 * prop2 (* Until2^-1*)

(* module FormulaSet = Set.Make (struct type t = prop2 let compare (p1:prop2) (p2:prop2)= if p1 <= p2 then -1 else if p1 = p2 then 0 else 1 end) *)


(* on-the-fly simplifications *)
let rec not2 = function
  | Not2 x -> x
  | False2 -> True2
  | True2 -> False2
  | And2 (p1, p2) -> Or2 (not2 p1, not2 p2)
  | Or2 (p1, p2) -> And2 (not2 p1, not2 p2)
  | Impl2 (p1, p2) -> And2 (p1, not2 p2)
  | Exists2 (x, t, p) -> Forall2 (x, t, not2 p)
  | Forall2 (x, t, p) -> Exists2 (x, t, not2 p)
  | x -> Not2 x
           
let and2 = function  
  | False2, x | x, False2 -> False2
  | True2, x | x, True2 -> x
  | x, y when x = y -> x
  | x, y -> And2 (x, y)

let or2 = function
  | True2, x | x, True2 -> True2
  | False2, x | x, False2 -> x
  | x, y when x = y -> x
  | x, y -> Or2 (x, y)

let impl2 = function
  | True2, True2 -> True2
  | False2, x
  | x, True2 -> True2
  | x, False2 -> not2 x
  | True2, x -> x
  | x, y when x = y -> True2
  | x, y -> Impl2 (x, y)


let rec iff2 = function
  | True2, True2
  | False2, False2 -> True2
  | True2, p
  | p, True2 -> p
  | False2, p
  | p, False2 -> not2 p
  | Not2 p1, Not2 p2 -> iff2 (p1, p2)
  | (p1, p2) -> Iff2 (p1, p2)


let forall2 x s = function
  | True2 -> True2
  | _ when s = Names.empty -> True2
  | p -> Forall2 (x, s, p)

let exists2 x s = function
  | False2 -> False2
  | _ when s = Names.empty -> False2
  | p -> Exists2 (x, s, p)

let const_pred2 (p, xs) =
  let name = p.pred_name in
  if name = Names.empty then
    False2
  else if name = Names.univ then
    True2
  else
    ConstPred2 (p, xs)
