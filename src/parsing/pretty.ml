(*******************************************************************************
 * Time-stamp: <2015-06-23 CEST 10:20:22 David Chemouil>>
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

open Batteries
open PPrint
open Ast.Expr
open Ast.Par
open Ast.Ctrl
open Ast.File
open Electrum

let comma_ = PPrint.(comma ^^ space)
let braces = PPrint.(enclose (lbrace ^^ space) (space ^^ rbrace))
let tab_size = 2
let comma_sep_map l = separate_map comma_ l

let rec expr_to_document (e : expr) =
  prim_expr_to_document (e.expr)

and prim_expr_to_document : prim_expr -> document = function
  | EThis ->
      string Kwd.this_
  | EConst c ->
      string @@ constant_to_string c
  | ELet (defs, block) ->
      string Kwd.let_
      ^^ space
      ^^ comma_sep_map def_to_document defs
      ^^ space
      ^^ block_or_bar_to_document block
  | EQuant (quant, decls, block) ->
      prefix tab_size 1
        ((string @@ enumerators_to_string (quant :> enumerators))
         ^^ space ^^ decls_to_document decls)
        (block_or_bar_to_document block)
  | EUnary (UPrime, e) ->
      expr_to_document e ^^ (string @@ unary_to_string UPrime)
  | EUnary (op, e) ->
      prefix tab_size 1
        (string @@ unary_to_string op) (expr_to_document e)
      |> parens
  | EBinary (e1, BDot, e2) ->
      flow empty [
        expr_to_document e1;
        string @@ binary_to_string BDot;
        expr_to_document e2
      ] 
  | EBinary (e1, op, e2) -> 
      infix tab_size 1
        (string @@ binary_to_string op)
        (expr_to_document e1)
        (expr_to_document e2)
      |> parens
  | ECart (e1, left, right, e2) ->
      flow space [
        expr_to_document e1;
        (string @@ enumerators_to_string (left :> enumerators));
        string Sym.arrow_;
        (string @@ enumerators_to_string (right :> enumerators));
        parens (expr_to_document e2)
      ] |> parens
  | EComp (e1, comp, e2) ->
      flow space [
        expr_to_document e1;
        (string @@ comparison_to_string comp);
        expr_to_document e2
      ]  
  | EIte (c, t, e) ->
      flow space [
        expr_to_document c;
        string Kwd.implies_;
        expr_to_document t;
        string Kwd.else_;
        expr_to_document e
      ]  
      |> parens
  | EApp (f, args) ->
      flow empty [
        expr_to_document f;
        brackets (comma_sep_map expr_to_document args)
      ]  
  | EAtName ident ->
      string "@" ^^ Ast_ident.to_document ident
  | EQualName qname ->
      Ast_qname.to_document qname
  | EBlock block ->
      block_to_document block
  | ECompr (decls, block) ->
      flow space [
        decls_to_document decls;
        block_or_bar_to_document block
      ] |> braces


and decls_to_document decls = comma_sep_map decl_to_document decls

and decl_to_document
      { is_variable; is_disjoint_variables; names; range; is_disjoint_ranges } =
  flow empty [
    if is_variable then
      string Kwd.var_ ^^ space
    else empty;
    if is_disjoint_variables then
      string Kwd.disj_ ^^ space
    else empty;
    comma_sep_map Ast_ident.to_document names;
    space;
    colon;
    space;
    if is_disjoint_ranges then
      string Kwd.disj_ ^^ space
    else empty;
    expr_to_document range
  ]

and def_to_document ({ name; expr } : def) =
  flow space [
    Ast_ident.to_document name;
    colon;
    expr_to_document expr
  ]

and block_to_document exprs =
  if exprs = [] then
    braces empty
  else
    surround_separate_map tab_size 1 empty lbrace hardline rbrace
      expr_to_document exprs

and block_or_bar_to_document exprs =
  match exprs with
    | [expr] ->
        flow space [
          bar;
          expr_to_document expr
        ]
    | ([] | _::_) -> block_to_document exprs  


let sig_ext_to_document = function
  | Extends qname ->
      string Kwd.extends_
      ^^ space ^^ Ast.Qname.to_document qname
  | In qnames ->
      string Kwd.in_
      ^^ space ^^
      separate_map (space ^^ string Sym.plus_ ^^ space)
        Ast.Qname.to_document qnames

let sig_to_document s =
  flow empty [
    if s.is_variable then
      string Kwd.var_ ^^ space
    else empty;
    if s.is_abstract then
      string Kwd.abstract_ ^^ space
    else empty;
    begin
      match s.mult with
        | None -> empty
        | Some m ->
            (string @@ enumerators_to_string (m :> enumerators)) ^^ space
    end;
    string Kwd.sig_;
    space;
    comma_sep_map Ast.Ident.to_document s.names;
    space;
    begin
      match s.extends with
        | None -> empty
        | Some ext -> sig_ext_to_document ext ^^ space
    end;
    if s.fields <> [] then
      braces @@
      nest tab_size (hardline ^^
                     separate_map (comma ^^ hardline) decl_to_document s.fields)
      ^^ hardline
    else PPrint.braces empty;
    begin
      match s.fact with
        | None -> empty
        | Some fact -> block_to_document fact
    end
  ]

let enum_to_document { name; cases } =
  flow empty [
    string @@ Kwd.enum_;
    space;
    comma_sep_map Ast.Ident.to_document cases;
    space;
    braces empty
  ]

let fact_to_document ({ name; body } : fact) =
  flow empty [
    string @@ Kwd.fact_;
    space;
    begin
      match name with
        | None -> empty
        | Some n -> Ast.Ident.to_document n ^^ space
    end;
    block_to_document body
  ]


let assert_to_document ({ name; body } : assertion) =
  flow empty [
    string @@ Kwd.assert_;
    space;
    begin
      match name with
        | None -> empty
        | Some n -> Ast.Ident.to_document n ^^ space
    end;
    block_to_document body
  ]


let pred_to_document ({ name; params; body } : pred) =
  flow empty [
    string @@ Kwd.pred_;
    space;
    Ast.Ident.to_document name;
    comma_sep_map decl_to_document params |> brackets;
    space;
    block_to_document body
  ]

let fun_to_document ({ name; params; returns; body } : func) =
  flow empty [
    string @@ Kwd.fun_;
    space;
    Ast.Ident.to_document name;
    comma_sep_map decl_to_document params |> brackets;
    space;
    colon;
    space;
    expr_to_document returns;
    space;
    expr_to_document body
  ]

let paragraph_to_document = function
  | Sig s -> sig_to_document s
  | Enum e -> enum_to_document e 
  | Fact f -> fact_to_document f 
  | Pred p -> pred_to_document p 
  | Fun f -> fun_to_document f 
  | Assert a -> assert_to_document a 


let cmd_type_to_document = function
  | Run -> string @@ Kwd.run_
  | Check -> string @@ Kwd.check_

let int_to_document n = string @@ string_of_int n


let typescope_to_document (exactly, num, sig_name) =
  flow empty [
    if exactly then (string @@ Kwd.exactly_) ^^ space
    else empty;
    int_to_document num;
    space;
    Ast.Qname.to_document sig_name
  ]

let scope_to_document = function
  | ForBut (num, typescopes) ->
      flow empty [
        string @@ Kwd.for_; 
        space;
        int_to_document num
      ]
      ^^      
      if typescopes <> [] then
        flow empty [
          space;
          string @@ Kwd.but_;
          space;
          comma_sep_map typescope_to_document typescopes
        ]
      else empty
  | ForTypes typescopes ->
      flow empty [
        string @@ Kwd.for_;
        space;
        comma_sep_map typescope_to_document typescopes
      ]

let nick_to_document nick =
  string (Ast.Ident.to_string nick) ^^ colon

let cmd_to_document = function
  | NamedCmd (qname, cmd, scope, nick) ->
      flow empty [
        Batteries.Option.map_default
          (fun x -> nick_to_document x ^^ space) empty nick;
        cmd_type_to_document cmd;
        space;
        Ast.Qname.to_document qname;
        space;
        Batteries.Option.map_default scope_to_document empty scope
      ]
  | BlockCmd (block, cmd, scope, nick) ->
      flow empty [
        cmd_type_to_document cmd;
        space;
        block_to_document block;
        space;
        Batteries.Option.map_default scope_to_document empty scope
      ]

let module_opt_to_document = function
  | None -> empty
  | Some (name, formals) ->
      flow empty [
        string @@ Kwd.module_;
        space;
        Ast.Qname.to_document name;
        if formals <> [] then
          comma_sep_map Ast.Qname.to_document formals |> brackets
        else empty;
        hardline
      ]

let import_to_document (mod_name, actuals, pun) = 
  flow empty [
    string @@ Kwd.open_;
    space;
    Ast.Qname.to_document mod_name;
    comma_sep_map Ast.Qname.to_document actuals |> brackets;
    Batteries.Option.map_default
      (fun x -> space ^^ string Kwd.as_ ^^ space ^^ Ast.Ident.to_document x)
      empty pun;    
    hardline
  ]

let par_cmd_to_document = function
  | Par par -> paragraph_to_document par
  | Cmd cmd -> cmd_to_document cmd

let file_to_document ((module_opt, imports, par_cmds) : file) =
  flow empty [
    module_opt_to_document module_opt;
    separate_map hardline import_to_document imports |> terminate hardline;
    separate_map (hardline ^^ hardline) par_cmd_to_document par_cmds
  ]


let print ?(ribbon=0.8) ?(width=80) ast =
  file_to_document ast
  |> enclose empty hardline
  |> Util.PPrintX.print ~ribbon ~width
