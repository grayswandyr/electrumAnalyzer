(*******************************************************************************
 * Time-stamp: <2015-03-05 CET 15:46:05 David Chemouil>
 * 
 * Electrum Analyzer 
 * Copyright (C) 2014-2015 Onera
 * Authors: 
 *   Denis Kuperberg <denis DOT kuperberg AT gmail DOT com>
 *   Julien Brunel <julien DOT brunel AT onera DOT fr>
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

type name = string

type op =
  | Plus
  | Minus

type comp =
  | Lte 
  | Lt
  | Gte
  | Gt
  | Eq 
  | Neq

type term =
  | TConst of int 
  | TBin of op * term * term 
  | TMult of int * term 
  | TCount of (prop list)
and  
  prop =
  | LTrue
  | LFalse
  | LAtom of name (*atomic proposition that may vary in time*)
  | LConstAtom of name (*atomic proposition that is constant*)
  | LComp of comp * term * term

  (* boolean operators *)
  | LNot of prop
  | LAnd of prop * prop
  | LOr of prop * prop
  | LImpl of prop * prop
  | LEquiv of prop * prop

  (* temporal (future) operators *)
  | LNext of prop
  | LAlways of prop
  | LEventually of prop
  | LUntil of prop * prop
  | LRelease of prop * prop

  (* temporal (past) operators *)
  | LPrevious of prop (* LNext^-1 *)
  | LHist of prop (* LAlways^-1 *)
  | LOnce of prop (* LEventually^-1 *)
  | LSince of prop * prop (* LUntil^-1*)

(* on-the-fly simplifications *)
let rec ltlnot = function
  | LNot x -> x
  | LFalse -> LTrue
  | LTrue -> LFalse
  | LAnd (p1, p2) -> LOr (ltlnot p1, ltlnot p2)
  | LOr (p1, p2) -> LAnd (ltlnot p1, ltlnot p2)
  | LImpl (p1, p2) -> LAnd (p1, ltlnot p2)
  | x -> LNot x
           
let ltland = function
  | LFalse, x | x, LFalse -> LFalse
  | LTrue, x | x, LTrue -> x
  | x, y when x = y -> x
  | x, y -> LAnd (x, y)

let ltlor = function
  | LTrue, x | x, LTrue -> LTrue
  | LFalse, x | x, LFalse -> x
  | LNot x, LNot y when x=y -> ltlnot x
  | x, y when x=y -> x
  | x, y -> LOr (x, y)

let rec limpl product =
  match product with
  | LTrue, LTrue -> LTrue
  | LFalse, x -> LTrue
  | x, LTrue -> LTrue
  | x, LFalse -> ltlnot x
  | LTrue, x -> x
  | x, y when x = y -> LTrue
  | x, LNot y when x = y -> ltlnot y 
  | LAnd (x, y), z when x = z -> LTrue
  | LAnd (x, y), z  when y = z -> LTrue 
  | LAnd (x,y), LNot z when x = z -> limpl (y, ltlnot z)
  | x, LImpl (y,z) -> limpl (ltland (x, y), z) 
  | x, y -> LImpl (x, y)

and lequiv product =
  match product with
  | LTrue, LTrue -> LTrue
  | LFalse, LFalse -> LTrue
  | x, LTrue | LTrue, x -> x
  | x, LFalse | LFalse, x -> ltlnot x
  | x, y when x = y -> LTrue
  | x, y -> LEquiv (x, y)
    
(* and simplify formula =  *)
(*   match formula with *)
(*   | LNot x -> ltlnot x *)
(*   | LAnd (p1, p2) -> ltland (p1, p2) *)
(*   | LOr (p1, p2) -> ltlor (p1, p2) *)
(*   | LImpl (p1, p2) -> limpl (p1, p2) *)
(*   | x -> x *)

(* replace the string str1 by str2 in (every occurrence of atom names of)  
   formula  
*)
let rec replace formula str1 str2 =
  match formula with 
  | LAtom n -> LAtom (Str.global_replace (Str.regexp str1) str2 n)
  | LConstAtom n -> LConstAtom (Str.global_replace (Str.regexp str1) str2 n) 
  | LNot x -> ltlnot (replace x str1 str2)
  | LFalse -> LTrue
  | LTrue -> LFalse
  | LComp (c, t1, t2) -> print_endline "Warning : Ltl.replace: integer comparison not handled yet"; LComp (c, t1, t2)
  | LAnd (p1, p2) -> ltland (replace p1 str1 str2, replace p2 str1 str2)
  | LOr (p1, p2) -> ltlor (replace p1 str1 str2, replace p2 str2 str2)
  | LImpl (p1, p2) -> limpl (replace p1 str1 str2, replace p2 str1 str2)
  | LEquiv (p1, p2) -> lequiv (replace p1 str1 str2, replace p2 str1 str2)
  | LNext p -> LNext (replace p str1 str2)
  | LAlways p ->  LAlways (replace p str1 str2)
  | LEventually p ->  LEventually (replace p str1 str2)
  | LUntil (p1, p2) -> LUntil (replace p1 str1 str2, replace p2 str1 str2)
  | LRelease (p1, p2) -> LRelease (replace p1 str1 str2, replace p2 str1 str2)
  | LPrevious p -> LPrevious (replace p str1 str2)
  | LHist p -> LHist (replace p str1 str2)
  | LOnce p -> LOnce (replace p str1 str2)
  | LSince (p1, p2) -> LSince (replace p1 str1 str2, replace p2 str1 str2)
                              
(* idem as replace, but for lists of strings *)
let rec replace_list formula str_list1 str_list2 =
  match formula with
  | LAtom n -> 
     let f acc s1 s2 =
       Str.global_replace (Str.regexp s1) s2 acc
     in
     let new_name = 
       List.fold_left2 f n str_list1 str_list2 
     in  
     LAtom (new_name)
  | LConstAtom n -> 
     let f acc s1 s2 =
       Str.global_replace (Str.regexp s1) s2 acc
     in
     let new_name = 
       List.fold_left2 f n str_list1 str_list2 
     in  
     LConstAtom (new_name)
  | LNot x -> ltlnot (replace_list x str_list1 str_list2)
  | LFalse -> LTrue
  | LTrue -> LFalse
  | LComp (c, t1, t2) -> LComp (c, t1 , t2) (* TODO *)
  | LAnd (p1, p2) -> ltland (replace_list p1 str_list1 str_list2, 
                             replace_list p2 str_list1 str_list2)
  | LOr (p1, p2) -> ltlor (replace_list p1 str_list1 str_list2, 
                           replace_list p2 str_list2 str_list2)
  | LImpl (p1, p2) -> limpl (replace_list p1 str_list1 str_list2, 
                             replace_list p2 str_list1 str_list2)
  | LEquiv (p1, p2) -> lequiv (replace_list p1 str_list1 str_list2, 
                               replace_list p2 str_list1 str_list2)
  | LNext p -> LNext (replace_list p str_list1 str_list2)
  | LAlways p ->  LAlways (replace_list p str_list1 str_list2)
  | LEventually p ->  LEventually (replace_list p str_list1 str_list2)
  | LUntil (p1, p2) -> LUntil (replace_list p2 str_list1 str_list2, 
                               replace_list p2 str_list1 str_list2)
  | LRelease (p1, p2) -> LRelease (replace_list p2 str_list1 str_list2, 
                                   replace_list p2 str_list1 str_list2)
  | LPrevious p -> LPrevious (replace_list p str_list1 str_list2)
  | LHist p -> LHist (replace_list p str_list1 str_list2)
  | LOnce p -> LOnce (replace_list p str_list1 str_list2)
  | LSince (p1, p2) -> LSince (replace_list p1 str_list1 str_list2, 
                               replace_list p2 str_list1 str_list2)
     


