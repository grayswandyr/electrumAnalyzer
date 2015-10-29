(*******************************************************************************
 * Time-stamp: <2015-07-22 CEST 17:20:52 David Chemouil>
 * 
 * Electrum Analyzer 
 * Copyright (C) 2014-2015 Onera
 * Authors: 
 *   Julien Brunel 
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
open Ltl
open PPrint

let infix = infix 2 1

let doc_lte = string "<="
let doc_lt = string "<"
let doc_gt = string ">"
let doc_gte = string ">="
let doc_eq = string "="
let doc_neq = string "!="

let doc_true = string "TRUE"
let doc_false = string "FALSE"

let doc_impl =string "->"
let doc_equiv =string "<->"

let doc_x = string "X"
let doc_f = string "F"
let doc_g = string "G"
let doc_u = string "U"
let doc_v = string "V"

let doc_y = string "Y"
let doc_h = string "H"
let doc_o = string "O"
let doc_s = string "S"

let doc_count = string "count"

let doc_module_main =
  flow space [ string "MODULE"; string "main" ]
  ^^ hardline
  ^^ flow space [ string "JUSTICE"; doc_true; semi ]

let doc_frozenvar = string "FROZENVAR"
let doc_boolean = string "boolean"

let doc_var = string "VAR"
let doc_invar = string "INVAR"
let doc_ltlspec = string "LTLSPEC"

module NameSet = Set.Make (struct type t = name let compare = compare end)

type ltl_document = {
  formula : document ;
  const_atoms : NameSet.t ;
  var_atoms : NameSet.t ;
}

let document_of_op o = match o with 
  | Plus -> plus
  | Minus -> minus

let document_of_comp c = match c with 
  | Lte -> doc_lte
  | Lt -> doc_lt
  | Gte -> doc_gte
  | Gt -> doc_gt
  | Eq  -> doc_eq
  | Neq -> doc_neq

let rec document_of_term t = match t with
  | TConst i -> 
      { formula = string (string_of_int i);
        const_atoms = NameSet.empty;
        var_atoms = NameSet.empty;
      }
  | TBin (o, t1, t2) ->
      let d1 = document_of_term t1 in
      let d2 = document_of_term t2 in
      { formula = infix (document_of_op o) d1.formula d2.formula;
        const_atoms = NameSet.union d1.const_atoms d2.const_atoms;
        var_atoms = NameSet.union d1.var_atoms d2.var_atoms;
      }
  | TMult (i, t1) ->
      let d1 = document_of_term t1 in
      { formula = infix star (string (string_of_int i)) d1.formula;
        const_atoms = d1.const_atoms;
        var_atoms = d1.var_atoms;
      }
  | TCount (formulalist) -> 
      let doclist = List.map document_of_prop formulalist in
      let formulas, const_ats, var_ats = 
        List.fold_right 
          (fun doc (acc_form, acc_const, acc_var) ->     
             doc.formula :: acc_form,
             (NameSet.union doc.const_atoms acc_const) , 
             (NameSet.union doc.var_atoms acc_var)
          )
          doclist
          ([], NameSet.empty, NameSet.empty)
      in
      { formula = doc_count ^^ (parens @@ separate comma formulas);
        const_atoms = const_ats;
        var_atoms = var_ats;
      }
and 
  document_of_prop prop = match prop with
  | LTrue -> { formula = doc_true ; 
               const_atoms = NameSet.empty ; 
               var_atoms = NameSet.empty ;
             }
  | LFalse -> { formula = doc_false ; 
                const_atoms = NameSet.empty ; 
                var_atoms = NameSet.empty ;
              }
  | LAtom n ->  
      { formula = string n ;
        const_atoms = NameSet.empty ;
        var_atoms = NameSet.singleton n ;
      }
  | LConstAtom n -> { formula = string n ;
                      const_atoms = NameSet.singleton n ;
                      var_atoms = NameSet.empty ;
                    }

  | LComp (c , t1 , t2) -> 
      let d1 = document_of_term t1 in
      let d2 = document_of_term t2 in
      { formula = 
          parens (d1.formula 
                  ^^ (document_of_comp c)
                  ^^ d2.formula) ;
        const_atoms = NameSet.union d1.const_atoms d2.const_atoms ;
        var_atoms = NameSet.union d1.var_atoms d2.var_atoms ;
      }

  | LNot p -> 
      let d = document_of_prop p in
      { d with formula = parens @@ bang ^//^ d.formula }

  | LAnd (p1 , p2) ->  
      let d1 = document_of_prop p1 and d2 = document_of_prop p2 in
      { formula = infix ampersand d1.formula d2.formula |> parens;
        const_atoms = NameSet.union d1.const_atoms d2.const_atoms ;
        var_atoms = NameSet.union d1.var_atoms d2.var_atoms ;
      }
  | LOr (p1 , p2) ->  
      let d1 = document_of_prop p1 and d2 = document_of_prop p2 in
      { formula = infix bar d1.formula d2.formula |> parens;
        const_atoms = NameSet.union d1.const_atoms d2.const_atoms ;
        var_atoms = NameSet.union d1.var_atoms d2.var_atoms ;
      }
  | LImpl (p1 , p2) -> 
      let d1 = document_of_prop p1 and d2 = document_of_prop p2 in
      { formula = infix doc_impl d1.formula d2.formula |> parens;
        const_atoms = NameSet.union d1.const_atoms d2.const_atoms ;
        var_atoms = NameSet.union d1.var_atoms d2.var_atoms ;
      }

  | LEquiv  (p1 , p2) -> 
      let d1 = document_of_prop p1 and d2 = document_of_prop p2 in
      { formula = infix doc_equiv d1.formula d2.formula |> parens;
        const_atoms = NameSet.union d1.const_atoms d2.const_atoms ;
        var_atoms = NameSet.union d1.var_atoms d2.var_atoms ;
      }

  | LNext p ->  
      let d = document_of_prop p in
      { d with formula = parens @@ doc_x ^//^ d.formula }
  | LAlways p -> 
      let d = document_of_prop p in
      { d with formula = parens @@ doc_g ^//^ d.formula }

  | LEventually p -> 
      let d = document_of_prop p in
      { d with formula = parens @@ doc_f ^//^ d.formula }
  | LUntil (p1 , p2) -> 
      let d1 = document_of_prop p1 and d2 = document_of_prop p2 in
      { formula = infix doc_u d1.formula d2.formula |> parens;
        const_atoms = NameSet.union d1.const_atoms d2.const_atoms ;
        var_atoms = NameSet.union d1.var_atoms d2.var_atoms ;
      }

  | LRelease (p1 , p2)-> 
      let d1 = document_of_prop p1 and d2 = document_of_prop p2 in
      { formula = infix doc_v d1.formula d2.formula |> parens;
        const_atoms = NameSet.union d1.const_atoms d2.const_atoms ;
        var_atoms = NameSet.union d1.var_atoms d2.var_atoms ;
      }

  | LPrevious p ->
      let d = document_of_prop p in
      { d with formula = parens @@ doc_y ^//^ d.formula }
  | LHist p -> 
      let d = document_of_prop p in
      { d with formula = parens @@ doc_h ^//^ d.formula }

  | LOnce p -> 
      let d = document_of_prop p in
      { d with formula = parens @@ doc_o ^//^ d.formula }
  | LSince (p1 , p2) -> 
      let d1 = document_of_prop p1 and d2 = document_of_prop p2 in
      { formula = infix doc_s d1.formula d2.formula |> parens;
        const_atoms = NameSet.union d1.const_atoms d2.const_atoms ;
        var_atoms = NameSet.union d1.var_atoms d2.var_atoms ;
      }
(* let record n = *)


let boolean_var elt =
  flow space [
    string elt;
    colon;
    doc_boolean
  ]
  ^^ semi
  ^^ hardline

let to_nusmv  ?(ribbon=0.8) ?(margin=80) ?invar:(inv_form=LTrue) 
      formula output_file_name =
  let oc = if output_file_name = "" then
      Legacy.stdout
    else
      Legacy.open_out output_file_name in
  let formula_doc = document_of_prop formula in 
  let invars_doc = document_of_prop inv_form in
  let preamble = doc_module_main in
  let frozen_var_decl = 
    precede 
      (doc_frozenvar ^^ hardline)
      (NameSet.fold (fun elt doc -> boolean_var elt ^^ doc) 
         (NameSet.union formula_doc.const_atoms invars_doc.const_atoms) 
         empty
      )
  in
  let var_decl = 
    precede 
      (doc_var ^^ hardline)
      (NameSet.fold (fun elt doc -> boolean_var elt ^^ doc) 
         (NameSet.union formula_doc.var_atoms invars_doc.var_atoms) 
         empty
      )  
  in
  let invar_decl =
    flow hardline [ doc_invar; invars_doc.formula ]
  in 
  let result = 
    flow hardline [
      preamble ;
      frozen_var_decl ;
      var_decl ;
      invar_decl;
      doc_ltlspec ;
      formula_doc.formula;
    ]
    ^^ hardline
  in
  ToChannel.pretty ribbon margin oc result;
  if output_file_name <> "" then Legacy.close_out oc

let ltl_to_string formula =
  Util.PPrintX.to_string @@ (document_of_prop formula).formula

let print ?(ribbon=0.8) ?(margin=80) ltldoc =
  ToChannel.pretty ribbon margin Legacy.stdout 
    ltldoc.formula

let print_ltl  ?(ribbon=0.8) ?(margin=80) formula =
  ToChannel.pretty ribbon margin Legacy.stdout 
    (document_of_prop formula).formula

