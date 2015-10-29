(*****************************************************************************
 * Time-stamp: <2015-10-27 CET 11:35:35 David Chemouil>
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
 ****************************************************************************)

(*****************************************************************************
 * ast.ml -- abstract syntax tree for Electrum
 ****************************************************************************)

open Batteries
open List

module Ident = Ast_ident
module Qname = Ast_qname
module Expr = Ast_expr
module Par = Ast_par
module Ctrl = Ast_ctrl
module File = Ast_file


module Alpha = struct
  open Ast_expr

  let fresh, reset =
    let start = (-1) in
    let count = ref start in
    let f ?(sep = "#") base =
      incr count;
      Printf.sprintf "%s%s%d" base sep !count
    in
    let r () = count := start
    in
    (f, r)

  let fresh_ident id = 
    Ast_ident.to_string id
    |> fresh
    |> Ast_ident.make

  let fresh_qname qn =
    Ast_qname.to_string qn
    |> fresh
    |> Ast_ident.make
    |> Ast_qname.update qn

  let subst_ident env id =
    if mem_assoc id env then
      assoc id env
    else id

  let subst_qname env qname =
    let id = subst_ident env (Ast_qname.to_ident qname) in
    Ast_qname.update qname id

  let print_renaming ren =
    map (fun (x, y) -> (Ast_ident.to_string x, Ast_ident.to_string y)) ren |>
    Util.ListX.to_string (Tuple2.print String.print String.print)

  (* poor man's state monad *)
  let return env data = (env, data)

  let rec rename (module_decl, imports, par_cmds) =
    (module_decl, imports, map rename_par par_cmds)

  and rename_par poc =
    let open Ast_file in
    let open Ast_par in
    match poc with
      | Par Pred f -> 
          let (env, pars)= refresh_decls [] f.params in
          Par (Pred { f with params=pars;
                             body = rename_block env f.body })
      | Par Fun f -> 
          let (env, pars)= refresh_decls [] f.params in
          Par (Fun { f with params=pars;
                            returns = rename_expr env f.returns;
                            body = rename_expr env f.body })
      | Par Fact f -> Par (Fact { f with body = rename_block [] f.body} )
      | Par Assert f -> Par (Assert { f with body = rename_block [] f.body} )
      | _ -> poc

  and rename_expr env exp =
    let expr2 = rename_prim_expr env exp.expr in
    { exp with expr = expr2 }

  and rename_block env block =
    map (rename_expr env %> (fun expr -> expr)) block

  and refresh_decl env decl = 
    (* create a fresh variable for every declared variable *)
    let renamings = map (fun id -> (id, fresh_ident id)) decl.names in
    return (rev renamings @ env)
      { decl with
          names = snd @@ split renamings;
          range = rename_expr env decl.range }

  and refresh_decls env decls =
    (* walk from left to right, accumulating an ever-expanding
       environment of renamings, starting from the initial environment
       env; and accumulating the list of already refreshed ranges *)
    let rec aux (acc_env, acc_decl) decls = match decls with
      | [] -> (acc_env, acc_decl)
      | decl :: tl ->
          let updated_env, updated_decl = refresh_decl acc_env decl in
          aux (updated_env, updated_decl :: acc_decl) tl
    in
    let new_env, decls = aux (env, []) decls in
    (* decls is reversed as we accumulated it in the wrong order (more efficient) *)
    (new_env, rev decls)

  and refresh_def env def = 
    let renaming = (def.name, fresh_ident def.name) in
    return (renaming :: env) @@ make_def (snd renaming) (rename_expr env def.expr)

  and refresh_defs env defs =
    let rec aux (acc_env, acc_def) defs = match defs with
      | [] -> (acc_env, acc_def)
      | def :: tl -> 
          let updated_env, updated_def = refresh_def acc_env def in
          aux (updated_env, updated_def :: acc_def) tl
    in
    let new_env, defs = aux (env, []) defs in
    (new_env, rev defs)

  and rename_prim_expr env expr = match expr with
    (* quantifiers introduce bindings *)
    | EQuant (quant, decls, block) ->
        let fresh_env, fresh_decls = refresh_decls env decls in
        EQuant (quant, fresh_decls, rename_block (fresh_env @ env) block)
    (* so do let's *)
    | ELet (defs, block) -> 
        let fresh_env, fresh_defs = refresh_defs env defs in
        ELet (fresh_defs, rename_block (fresh_env @ env) block) 
    (* and comprehensions too *)
    | ECompr (decls, block) -> 
        let fresh_env, fresh_decls = refresh_decls env decls in
        ECompr (fresh_decls, rename_block (fresh_env @ env) block)
    (* qnames and idents are substituted *)
    | EQualName qn -> EQualName (subst_qname env qn)
    | EAtName id -> EAtName (subst_ident env id)
    (* remainder: structural recursion *)
    | EComp (e1, op, e2) ->
        EComp (rename_expr env e1, op, rename_expr env e2)
    | EIte (c, t, e) ->
        EIte (rename_expr env c, rename_expr env t, rename_expr env e)
    | EUnary (op, e) -> EUnary (op, rename_expr env e)
    | EBinary (e1, op, e2) -> EBinary (rename_expr env e1, op, rename_expr env e2)
    | EBlock block -> EBlock (rename_block env block)
    | EApp (f, exprs) -> EApp (rename_expr env f, rename_block env exprs) (* Warning : (denis) f was not renamed *)
    | ECart (e1, m1, m2, e2) -> ECart (rename_expr env e1, m1, m2, rename_expr env e2) 
    | EThis
    | EConst _ -> expr
end


module Hull = struct 
  open Ast_file
  open Ast_par

  let hull = "_Hull"

  let to_hull id = Ast_ident.make @@ hull ^ "_" ^ Ast_ident.to_string id

  let is_hull s = Str.string_match (Str.regexp hull) s 0

  let from_hull s = Str.string_after s (1+String.length hull)


  (* returns the signature that is the hull of the signature of name sig_name *) 
  let hull_of_sig sig_name =
    {
      is_variable = false;
      is_abstract = false;
      mult = None;
      names = [to_hull sig_name];
      extends = None;
      fields = [];
      fact = None;
    }


  (* if several (primary and variable) signarues are defined simmultaneously 
     (a signature with multiple  names), this function returns a list of 
     signatures, each  with a single name, and their hull signature, as a list of 
     Ast_file.par_cmd.
  *)      
  let unfold_signature s = 
    (* auxiliary function *)
    let rec unfold_sig s (name_list: Ast_ident.t list) =
      match name_list with
        | n :: tl -> 
            let hs = hull_of_sig (n) in
            let new_s = { s with names = [n]; 
                                 extends =Some (Extends (Ast_qname.make ~this:false ~path:[] ~name:(to_hull (n)))) ;
                        } 
            in
            Par (Sig hs) :: (Par (Sig new_s) :: unfold_sig s tl)
        | [] ->[] 
    in 

    if s.is_variable && s.extends = None 
    then
      unfold_sig s s.names
    else
      [Par (Sig s)]

  let rec add_hull_in_par par_cmd_list =
    match par_cmd_list with
      | [] -> []
      | Cmd c :: tl ->  Cmd c :: add_hull_in_par tl
      | Par (Sig s) :: tl -> 
          let unfold_s = unfold_signature s in
          unfold_s @ (add_hull_in_par tl)
      | Par p :: tl -> (Par p) :: add_hull_in_par tl


  let add_hull file =
    match file with
      | m, i, par_cmd_list -> m, i,
                              add_hull_in_par par_cmd_list

end
