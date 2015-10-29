(*******************************************************************************
 * Time-stamp: <2015-02-23 CET 17:59:34 David Chemouil>
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


module StringSet = Set.Make(String)

(* Electrum keywords *)
module Kwd = struct
  let abstract_ = "abstract"  
  let all_ = "all"  
  let and_ = "and"  
  let as_ = "as"  
  let assert_ = "assert"  
  let but_ = "but"  
  let check_ = "check"  
  let disj_ = "disj"  
  let else_ = "else"  
  let enum_ = "enum"  
  let exactly_ = "exactly"  
  let extends_ = "extends"  
  let fact_ = "fact"  
  let for_ = "for"  
  let fun_ = "fun"  
  let iden_ = "iden"  
  let iff_ = "iff"  
  let implies_ = "implies"  
  let in_ = "in"  
  let int_ = "Int"  
  let let_ = "let"  
  let lone_ = "lone"  
  let module_ = "module"  
  let no_ = "no"  
  let none_ = "none"  
  let not_ = "not"  
  let one_ = "one"  
  let open_ = "open"  
  let or_ = "or"  
  let pred_ = "pred"  
  let run_ = "run"  
  let set_ = "set"  
  let sig_ = "sig"  
  let some_ = "some"  
  let sum_ = "sum"
  let this_ = "this"
  let univ_ = "univ"
  let var_ = "var"

  let keywords = StringSet.of_list [
        abstract_;  all_;  and_;  as_;  assert_;  but_;  check_;  disj_;
        else_;  exactly_;  extends_;  fact_;  for_;  fun_;  iden_;  iff_;
        implies_;  in_;  int_;  let_;  lone_;  module_;  no_;  none_;  not_;
        one_;  open_;  or_;  pred_;  run_;  set_;  sig_;  some_;  sum_; this_;
        univ_;  var_
      ]
end

(* Electrum symbols *)
module Sym = struct
  let and_ = "&&"  
  let arrow_ = "->"
  let at_ = "@"
  let bar_ = "|"
  let card_ = "#"
  let colon_ = ":"
  let comma_ = ","
  let dot_ = "."
  let eq_ = "="
  let gt_ = ">"
  let gte_ = ">="
  let hat_ = "^"
  let iff_ = "<=>"
  let implies_ = "=>"
  let inter_ = "&"
  let lbrace_ = "{"
  let lbracket_ = "["
  let lparen_ = "("
  let lproj_ = "<:"
  let lt_ = "<"
  let lte_ = "=<"
  let minus_ = "-"
  let neq_ = "!="
  let or_ = "||"  
  let override_ = "++"
  let plus_ = "+"
  let prime_ = "'"
  let rbrace_ = "}"
  let rbracket_ = "]"
  let rparen_ = ")"
  let rproj_ = ":>"
  let slash_ = "/"
  let star_ = "*"
  let tilde_ = "~"
end


