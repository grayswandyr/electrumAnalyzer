(*******************************************************************************
 * Time-stamp: <2015-10-29 CET 15:50:57 David Chemouil>

   Electrum Analyzer 
   Copyright (C) 2014-2015 Onera 
   Authors: 
   Julien Brunel 

   This file is part of the Electrum Analyzer.

   The Electrum Analyzer is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by the Free
   Software Foundation, either version 3 of the License, or (at your option) any
   later version.

   The Electrum Analyzer is distributed in the hope that it will be useful, but
   WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
   FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
   details.

   You should have received a copy of the GNU General Public License along with
   the Electrum Analyzer.  If not, see <http://www.gnu.org/licenses/>.
 *****************************************************************************)

open Batteries
open K2
open K1
open Ltl
open Ltl_to_smv
open Names
open Profile
open K2PPrint
open PPrint
open Util


(* maps a name (of a variable) to a name (of an atom) *) 
type unfold_env = name NameMap.t

module ListSet = 
  Set.Make (struct type t = int list let compare = List.compare Int.compare end)

(*let rec find_bound scopes s = 
  match scopes with
  | [] -> failwith "no bound associated to this sort"
  | (_, k, s) :: q -> k
  | (_, _, s2) :: q (*where s <> s2*) -> find_bound q s
*)

let conj  phi1 phi2 = 
  ltland (phi1, phi2)

let disj  phi1 phi2 = 
  ltlor (phi1, phi2)

let conjunction formula_list =
  match formula_list with
    | [] -> Cfg.print_debug "Warning: conjunction of an empty formula list";
        LTrue 
    | t::q ->  List.fold_left conj t q

let disjunction formula_list =
  match formula_list with
    | [] ->Cfg.print_debug "Warning: disunction of an empty formula list";
        LFalse
    | t::q ->  List.fold_left disj t q


let atom_is_in s inst =
  inst ^ "_is_in_" ^ s


(* let rec compute_atoms_per_non_primary_sig sigenv current_map = *)
(*   if NameSet.equal  *)
(*        (NameSet.of_enum (NameMap.keys already_treated)) *)
(*        (NameSet.of_enum (NameMap.keys (fst sigenv.sigord))) *)
(*   then current_map *)

(* create a name as a concatenation of all the names in a list, 
   separated by "_"*)
let atomic_prop_name_from_list_name lname = 
  String.concat "_" lname

(*  create a variable atomic proposition (of LTL) from a predicate call, 
    given an unfolding environment associating each variable to an atom *)  
let atomic_proposition_from_pred unfolding_env p (nlist: string list) =
  match p with
    | { pred_name = pname; _} -> 
        (match nlist with 
          | [] -> LAtom pname
          | t::q ->
              if pname <> Names.ident then
                LAtom 
                  (pname ^ "_" 
                   ^ (atomic_prop_name_from_list_name 
                        (List.map (fun a ->
                               try 
                                 (NameMap.find 
                                    a unfolding_env)
                               with
                                 | Not_found -> 
                                     failwith ("atomic_proposition_from_pred " 
                                               ^ pname ^ ": variable " ^ a ^ 
                                               " not found in unfolding environment.")
                             ) 
                            nlist
                        )
                     ) )
              else (* interpret the identity relation as equality *)
                match nlist with
                  |[x;y] -> if NameMap.find x unfolding_env = NameMap.find y unfolding_env
                      then LTrue else LFalse
                  | _ -> failwith "K2_to_LTL: Identity must take two arguments"
        )


(*  create a constant atomic proposition (of LTL) from a predicate call, 
    given an unfolding environment associating each variable to an atom*)  
let atomic_proposition_from_const_pred unfolding_env p (nlist: string list) =
  match p with
    | { pred_name = pname; _} -> 
        (match nlist with 
          | [] -> LConstAtom pname
          | t::q -> 
              if pname <> Names.ident then
                LConstAtom 
                  (pname ^ "_" 
                   ^ (atomic_prop_name_from_list_name 
                        (List.map (fun a -> 
                               try
                                 (NameMap.find 
                                    a unfolding_env)
                               with
                                 |Not_found -> failwith ("atomic_proposition_from_const_pred " ^ pname ^ 
                                                         ": variable " ^ a ^ 
                                                         " not found in unfolding environment.")
                             ) 
                            nlist))
                  )
              else (* interpret the identity relation as equality *)
                match nlist with
                  |[x;y] -> if NameMap.find x unfolding_env = NameMap.find y unfolding_env
                      then LTrue else LFalse
                  | _ -> failwith "K2_to_LTL: Identity must take two arguments"
        )

(* replace each signature s in a profile by the list of the instances 
   of the primary sig of s.
   Used in the case of a cardinal term translation.
*)
let instantiate_profile sigenv prof =
  let instantiate_sig s =
    try
      NameMap.find s sigenv.instances_map
    with
    | Not_found -> failwith ("k2_to_ltl.instantiate_profile: canno instantiate \ 
                              signature " ^ s)
    (* let prim_of_s = primary_sig_of sigenv s in *)
    (* create_atoms (snd (NameMap.find prim_of_s sigenv.sigbounds)) prim_of_s *)
  in
  List.map (fun range -> List.map instantiate_sig range) (Union.elements prof)

let k2_int_op_to_ltl_int_op (o : K2.int_op2) =
  match o with 
    | Add2 -> Ltl.Plus
    | Sub2 -> Ltl.Minus

let comp2_to_ltl_comp (c: K2.comp_int2) =
  match c with 
    | Lte2 -> Ltl.Lte
    | Lt2 -> Ltl.Lt
    | Gte2 -> Ltl.Gte
    | Gt2 -> Ltl.Gt
    | Eq2  -> Ltl.Eq
    | Neq2 -> Ltl.Neq



(* This function translates a K2 formula into an LTL formula.
   Parameter unfolding_env maps a variable name to an atom.  
   Parameter sigenv is of type Profile.sig_env 
   Parameter phi is the K2 formula to translate.  
*)
let rec k2_to_ltl unfolding_env sigenv phi  =
  (* print_endline "Lower bounds:"; *)
  (* print_lowerbounds sigenv.lowerbounds; *)
  (* print_endline "Bounds:"; *)
  (* print_bound sigenv.sigbounds; *)
  (* the list of all signatures *)
  let siglist = List.of_enum (NameMap.keys (fst sigenv.sigord)) in

  (* the list of all the priamary signatures *)
  let primary_sigs = List.filter (is_primary sigenv) siglist in

  (* map associating each primary signature to the list of its intances 
     (atoms) *) 
  let atom_list_per_sig = 
    sigenv.instances_map
  in  

  (* returns the set of atoms in the primary signature subsuming s *)
  let instantiate s =
    (* print_endline ("Instantiating " ^s); *)
    try 
      if s = Names.univ
      then
        begin
          Cfg.print_debug "instantiate univ";
          NameMap.filter (fun k v -> List.mem k primary_sigs) atom_list_per_sig
         |> NameMap.values  |> List.of_enum |> List.concat
        end
      else
        NameMap.find  s atom_list_per_sig
    with
        Not_found -> failwith ("k2_to_ltl: cannot instantiate sort " ^ s)
  in

  match phi with 
    | True2 -> LTrue
    | False2 -> LFalse
    | Equal2 (n1 , n2) -> 
        if (compare (
              try NameMap.find n1 unfolding_env
              with Not_found -> failwith ("k_2_to_ltl: variable " ^ n1 ^ 
                                          " not found in unfolding environment.")
            ) 
              (try NameMap.find n2 unfolding_env
               with Not_found -> failwith ("k_2_to_ltl: variable " ^ n1 ^ 
                                           " not found in unfolding environment."))) = 0 
        then 
          LTrue
        else 
          LFalse
    | Comp2 (comp , t1 , t2) ->
        LComp (comp2_to_ltl_comp comp, term2_to_ltl_term unfolding_env sigenv t1, 
               term2_to_ltl_term unfolding_env sigenv t2)
    | ConstPred2 (p , nlist) -> 
        atomic_proposition_from_const_pred unfolding_env p nlist
    | VarPred2 (p , nlist) ->
        atomic_proposition_from_pred unfolding_env p nlist

    (* propositional connectives *)
    | Not2 p ->
        ltlnot (k2_to_ltl unfolding_env sigenv p)
    | And2 (p1 , p2) ->
        ltland (k2_to_ltl unfolding_env sigenv p1 , 
                k2_to_ltl unfolding_env sigenv  p2)
    | Or2 (p1 , p2) ->
        ltlor (k2_to_ltl unfolding_env sigenv p1 , 
               k2_to_ltl unfolding_env sigenv p2)
    | Impl2 (p1 , p2) ->
        limpl (k2_to_ltl unfolding_env sigenv p1 , 
               k2_to_ltl unfolding_env sigenv p2)
    | Iff2 (p1 , p2) ->
        lequiv (k2_to_ltl unfolding_env sigenv p1 , 
                k2_to_ltl unfolding_env sigenv p2)
    (* quantifiers *)
    | Forall2 (x, s, p) -> 

        if s = Names.univ
        then
          let list_of_forall = 
            List.map (fun sign -> k2_to_ltl unfolding_env sigenv (forall2 x sign p)) 
              primary_sigs 
          in
          conjunction list_of_forall

        else
          (* var_name_list = the list of the atoms corresponding of all instances
             of the primary signature subsuming s *)
          let var_name_list = instantiate s in
          let sons_for_extends = 
            List.filter (fun son -> is_father_for_extends sigenv.sigord son s)
                        siglist 
          in
          let sons_are_static_one_sigs =
            List.for_all (fun son ->
                          mult_is_one sigenv son
                          && not (is_var sigenv son)
                         )
                         sons_for_extends
          in
          
          let formula_list =
            (* static one sig, or abstract sig with all sons static one sigs (and no parent through in) *)
            (* formula_list = [p{x->s$1} ; p{x-> s$2} ; ...] *)
            if ((not (is_var sigenv s) &&  mult_is_one sigenv s)
               ||
                 (List.mem s sigenv.abstract_sigs && not (is_var sigenv s)
                  && sons_are_static_one_sigs)
               )
               && no_parent_through_in sigenv.sigord s
            then
              List.map (add_atom_to_env unfolding_env sigenv p x) 
                       var_name_list
            else
              (* exact bound *)
              if fst (NameMap.find (primary_sig_of sigenv s) sigenv.sigbounds)
              then
                begin
                  (* formula_list = [p{x->s$1} ; p{x-> s$2} ; ...] *) 
                  if (List.mem  s primary_sigs) 
                  then
                    List.map (add_atom_to_env unfolding_env sigenv p x) 
                             var_name_list
                  else
                    (* formula_list = [s$1_in_s => p{x->s$1} ; s$2_in_s => p{x-> s$2} ; ...] *) 
                    List.map (impl_forall_exact_bound unfolding_env sigenv x s p) 
                             var_name_list 
                end      
                  (* not exact bound *)
              else
                begin
                  if (List.mem s primary_sigs) then
                    begin
                      (* Cfg.print_debug @@ Printf.sprintf "Passage dans l'appel avec x = %s et s =%s\n" *)
                      (*            x s ; *)
                      (* formula_list = [s$1 => p{x-> s$1} ; s$2  -> p{x->s$2} ; ...] *)
                      List.map (create_implication unfolding_env sigenv x s p) 
                               var_name_list   
                    end
                  else
                    (* formula_list = [s$1 & s$1_in_s => p{x-> s$1} ; 
                     s$2 & s$2_in_s -> p{x->s$2}; ...] *)
                    List.map (impl_forall_notexact_bound unfolding_env sigenv x s p) 
                             var_name_list    
                end
          in       
          conjunction formula_list


    (* Quantifiers *)
    | Exists2 (x, s, p) -> 
        if s = Names.univ
        then
          let list_of_exists = 
            List.map (fun sign -> k2_to_ltl unfolding_env sigenv (exists2 x sign p)) 
              primary_sigs 
          in
          disjunction list_of_exists

        else 
          (* var_name_list = the list of the atoms corresponding of all instances
             of the primary signature subsuming s *) 
          let var_name_list = instantiate s in

          let sons_for_extends = 
            List.filter (fun son -> is_father_for_extends sigenv.sigord son s)
                        siglist 
          in
          let sons_are_static_one_sigs =
            List.for_all (fun son ->
                          mult_is_one sigenv son
                          && not (is_var sigenv son)
                         )
                         sons_for_extends
          in
          
          let formula_list =
            (* static one sig, or abstract sig with all sons static one sigs (and no parent through in) *)
            (* formula_list = [p{x->s$1} ; p{x-> s$2} ; ...] *)
            if ((not (is_var sigenv s) &&  mult_is_one sigenv s)
               ||
                 (List.mem s sigenv.abstract_sigs && not (is_var sigenv s)
                  && sons_are_static_one_sigs)
               )
               && no_parent_through_in sigenv.sigord s
            then
              List.map (add_atom_to_env unfolding_env sigenv p x) 
                       var_name_list
            else

              if fst (NameMap.find (primary_sig_of sigenv s) sigenv.sigbounds) 
              then
                begin
                  (* exact bound *)         
                  if List.mem s primary_sigs                              
                  then
                    (* exact bound and primary sig*)
                    (* formula_list = [p{x->s$1} ; p{x-> s$2} ; ...] *) 
                    List.map (add_atom_to_env unfolding_env sigenv p x) 
                             var_name_list 
                  else
                  (* formula_list = [s$1_in_s & p{x->s$1} ; s$2_in_s & p{x-> s$2} ; ...] *) 
                    List.map (conj_exists_exact_bound unfolding_env sigenv x s p) 
                             var_name_list
                end
              else
                (* not exact bound *)
                if List.mem s primary_sigs
                then
                  (* formula_list = [s$1 & p{x-> s$1} ; s$2 & p{x->s$2} ; ...] *)
                  List.map (create_conjunction unfolding_env sigenv x s p) 
                           var_name_list 
                else
                  (* formula_list = [s$1 & s$1_in_s & p{x-> s$1} ; s$2 & s$2_in_s & p{x->s$2} 
                   ; ...] *)
                  List.map (conj_exists_notexact_bound unfolding_env sigenv x s p) 
                           var_name_list
          in
          disjunction formula_list 

    (* (future) temporal connectives *)
    | Next2 p -> 
        LNext (k2_to_ltl unfolding_env sigenv p)
    | Always2 p -> 
        LAlways (k2_to_ltl unfolding_env sigenv p)
    | Eventually2 p -> 
        LEventually (k2_to_ltl unfolding_env sigenv p)
    | Until2 (p1 , p2) -> 
        LUntil (k2_to_ltl unfolding_env sigenv p1 , 
                k2_to_ltl unfolding_env sigenv p2)
    | Release2 (p1 , p2) -> 
        LRelease (k2_to_ltl unfolding_env sigenv p1 , 
                  k2_to_ltl unfolding_env sigenv p2)
    (* (past) temporal connectives *)
    | Previous2 p ->
        LPrevious (k2_to_ltl unfolding_env sigenv p)
    | Hist2 p ->
        LHist (k2_to_ltl unfolding_env sigenv p)
    | Once2 p ->
        LOnce (k2_to_ltl unfolding_env sigenv p)
    | Since2 (p1, p2) ->
        LSince (k2_to_ltl unfolding_env sigenv p1 , 
                k2_to_ltl unfolding_env sigenv p2)

and

  term2_to_ltl_term unfolding_env sigenv (t : K2.term2) =
  match t with 
    | TConst i -> Ltl.TConst i  
    | TBin (op , t1 , t2) -> 
        Ltl.TBin (k2_int_op_to_ltl_int_op op, 
                  term2_to_ltl_term unfolding_env sigenv t1 , 
                  term2_to_ltl_term unfolding_env sigenv t2)
    | TMult (i , t) ->
        Ltl.TMult (i , term2_to_ltl_term unfolding_env sigenv t)
    | TCard (xs, phi, prof) ->
        if Union.is_empty prof
        then 
          failwith ("k2_to_ltl.term2_to_ltl_term: profile is empty in a \ 
                    cardinal term.")
        else
          let l = List.length xs in
          if Union.exists (fun r -> (List.length r <> l)) prof
          then
            failwith ("k2_to_ltl.term2_to_ltl_term: profile is not coherent in a \ 
                      cardinal term.")
          else
            (* prof = [[s1; s2]; [s3;  s4]]
               prof_instantiated = [[[s1$1; s1$2]; [s2$1]] ; [[s3$1]; [s4$1; s4$2]]]
               xs_values = [[[s1$1; s2$1]; [s1$2; s2$1]]; [[s3$1; s4$1]; [s3$1; s4$2]]]
            *)
            let prof_instantiated = instantiate_profile sigenv prof in
            let xs_values = 
              (*List.flatten @@*)List.map List.n_cartesian_product 
                                   prof_instantiated
            in

            (*generation of a set of LTL formulas (one for each tuple in xs_values) *)
            Ltl.TCount(
              List.map2 
                (fun tuplelist range ->
                   List.map 
                     (fun tuple ->
                        let new_unfold_env =
                          List.fold_right2 
                            (fun inst var acc_unfold_env2 ->
                               NameMap.add var inst acc_unfold_env2
                            )
                            tuple xs
                            unfolding_env
                        in

                        let inst_constraints =
                          List.fold_right2
                            (fun inst s acc_formula ->
                               let ex_b = 
                                 fst @@ NameMap.find (primary_sig_of sigenv s) 
                                          sigenv.sigbounds
                               in
                               let prim = is_primary sigenv s in
                               let var = is_var sigenv s in
                               match (ex_b, prim, var) with
                                 | true, true, _ -> acc_formula
                                 | _, false, true -> ltland 
                                                       (LAtom (atom_is_in s inst),
                                                        acc_formula)
                                 | _, false, false -> ltland 
                                                        (LConstAtom (atom_is_in s inst),
                                                         acc_formula)
                                 | false, true, true -> ltland 
                                                          (LAtom inst,
                                                           acc_formula)
                                 | false, true, false -> ltland 
                                                           (LConstAtom inst,
                                                            acc_formula)
                            )
                            tuple range
                            LTrue
                        in
                        (* NameMap.print BatString.print BatString.print stdout new_unfold_env;              *)
                        ltland 
                          (inst_constraints, k2_to_ltl new_unfold_env sigenv phi)
                     )
                     tuplelist
                )
                xs_values
                (Union.elements prof)
              |> List.flatten
            )

and 
  impl_forall_exact_bound unfolding_env sigenv x s p atom =
  if (is_var sigenv s)
  then
    begin
      limpl 
        (LAtom (atom_is_in s atom),
         (add_atom_to_env unfolding_env sigenv p x atom) )
    end
  else
    limpl 
      (LConstAtom (atom_is_in s atom),
       (add_atom_to_env unfolding_env sigenv p x atom) )
and
  create_implication unfolding_env sigenv x s p atom =
  if (is_var sigenv s)
  then
    (
      limpl 
        (LAtom atom, 
         k2_to_ltl (NameMap.add x atom unfolding_env) sigenv p)
    )
  else
    limpl
      (LConstAtom atom,
       k2_to_ltl (NameMap.add x atom unfolding_env) sigenv p)
and
  impl_forall_notexact_bound unfolding_env sigenv x s p atom =
  let svar, prim_s_var = (is_var sigenv s, is_var sigenv (primary_sig_of sigenv s)) in
  match svar, prim_s_var with
    | true, true ->
        limpl 
          (ltland (LAtom atom, LAtom (atom_is_in s atom)), 
           k2_to_ltl (NameMap.add x atom unfolding_env) sigenv p)
    | true, false ->
        limpl 
          (ltland (LConstAtom atom, LAtom (atom_is_in s atom)), 
           k2_to_ltl (NameMap.add x atom unfolding_env) sigenv p)
    | false, true ->
        limpl 
          (ltland (LAtom atom, LConstAtom (atom_is_in s atom)), 
           k2_to_ltl (NameMap.add x atom unfolding_env) sigenv p)
    | false, false ->
        limpl 
          (ltland (LConstAtom atom, LConstAtom (atom_is_in s atom)), 
           k2_to_ltl (NameMap.add x atom unfolding_env) sigenv p)
and
  conj_exists_exact_bound unfolding_env sigenv x s p atom =
  if (is_var sigenv s)
  then
    ltland 
      (LAtom (atom_is_in s atom), 
       k2_to_ltl (NameMap.add x atom unfolding_env) sigenv p)
  else
    ltland 
      (LConstAtom (atom_is_in s atom), 
       k2_to_ltl (NameMap.add x atom unfolding_env) sigenv p)
and 
  conj_exists_notexact_bound unfolding_env sigenv x s p atom =
  let svar, prim_s_var = (is_var sigenv s, is_var sigenv (primary_sig_of sigenv s)) in
  match svar, prim_s_var with
    | true, true ->
        ltland 
          (ltland (LAtom (atom_is_in s atom), LAtom atom),
           k2_to_ltl (NameMap.add x atom unfolding_env) sigenv p)
    | true, false ->
        ltland 
          (ltland (LAtom (atom_is_in s atom), LConstAtom atom),
           k2_to_ltl (NameMap.add x atom unfolding_env) sigenv p)
    | false, true ->
        ltland 
          (ltland (LConstAtom (atom_is_in s atom), LAtom atom),
           k2_to_ltl (NameMap.add x atom unfolding_env) sigenv p)
    | false, false ->
        ltland 
          (ltland (LConstAtom (atom_is_in s atom), LConstAtom atom),
           k2_to_ltl (NameMap.add x atom unfolding_env) sigenv p)

and 
  create_conjunction unfolding_env sigenv x s p atom =
  if (is_var sigenv s)
  then
    (
      ltland 
        (LAtom atom, 
         k2_to_ltl (NameMap.add x atom unfolding_env) sigenv p)
    )
  else
    (
      ltland 
        (LConstAtom atom, 
         k2_to_ltl (NameMap.add x atom unfolding_env) sigenv p)
    ) 
and 
  add_atom_to_env unfolding_env sigenv p x atom =
  k2_to_ltl (NameMap.add x atom unfolding_env) sigenv p 

let translate sigenv phi =
  k2_to_ltl NameMap.empty sigenv phi

let print ?(ribbon=0.8) ?(margin=80) doc = 
  ToChannel.pretty ribbon margin Legacy.stdout doc

let print_ltl_formula  ?(ribbon=0.8) ?(margin=80) formula =
  ToChannel.pretty ribbon margin Legacy.stdout 
    (Ltl_to_smv.document_of_prop formula).formula

(* compute the list of ltl formulas related to the presence of an
   instance and the fact an instance is in a subsort 
*)

let compute_instances_constraints sigenv =
  (* the list of all signatures *)
  let siglist = List.of_enum (NameMap.keys (fst sigenv.sigord)) in

  (* the list of all the priamary signatures *)
  let primary_sigs = List.filter (is_primary sigenv) siglist in

  (* map associating each primary signature to the list of its intances 
     (atoms) *) 
  let atom_list_per_sig = 
    compute_atoms_per_sig sigenv.sigord sigenv.sigbounds
                          sigenv.sigmult sigenv.lowerbounds sigenv.abstract_sigs
  in  

  let subs_included_in_super_sig s =
    (* s must be primary *)
    (* if the bound is exact then there is no constraint *)
    if (fst (NameMap.find s sigenv.sigbounds))
    then 
      LTrue
    else
      let s_var = is_var sigenv s in

      (* list of subsigs that are not static one sigs *)
      let sub_sorts = 
        List.filter (fun x -> (is_father sigenv x s) && x <> Names.empty
                              && (not (mult_is_one sigenv x) || is_var sigenv x)
                    )
                    siglist 
      in
      let insts_of_s = 
        try
          NameMap.find s atom_list_per_sig
        with
            Not_found -> 
              failwith ("k2_to_ltl: subs_included_in_super_sig: cannot find instances \ 
                     of sort "^s)
      in
      let create_base_formula inst subsort =
        let sub_var =  is_var sigenv subsort in
        match s_var, sub_var with
          | true, true -> limpl (LAtom (atom_is_in subsort inst)
                                , LAtom (inst))
          | true, false -> limpl (LConstAtom (atom_is_in subsort inst)
                                 , LAtom (inst))
          | false, true -> limpl (LAtom (atom_is_in subsort inst)
                                 , LConstAtom (inst))
          | false, false -> limpl (LConstAtom (atom_is_in subsort inst)
                                  , LConstAtom (inst))
      in
      let formula_for_inst inst =
        if sub_sorts = [] 
        then
          LTrue
        else
          List.map (create_base_formula inst) sub_sorts |> conjunction
      in 
      if insts_of_s = []
      then
        LTrue
      else
        List.map formula_for_inst insts_of_s |> conjunction

  in     
  List.map subs_included_in_super_sig primary_sigs |> conjunction




(*  (\* Functions to help instantiation of subsorts *\) *)
(* let add_to_list_set n listset = *)
(*   ListSet.map (List.cons n) listset  *)

(* (\* computes the list [n; ...; n] *\) *)
(* let rec generate_const_list n length = *)
(*   match length with *)
(*   | 0 -> [] *)
(*   | l -> n::(generate_const_list n (l-1)) *)

(* (\* computes the list [0; 1; ... ; max] *\) *)
(* let rec generate_int_list max = *)
(*   match max with *)
(*   | 0 -> [0] *)
(*   | n -> n :: generate_int_list (n-1) *)

(* (\* computes the set of the lists that represent a partition of [0..n] in k subsets *\) *)
(* (\* each integer in the list represents the size of its corresponding subset *\) *)
(* (\* a list [2; 1; 3] represents the partition {0; 1} {2} {3; 4; 5} *\) *)
(* let rec generate_partitions n k = *)
(*   match (n,k) with *)
(*   | 0,k -> ListSet.singleton (generate_const_list 0 k) *)
(*   | n,1 -> ListSet.singleton ([n]) *)
(*   | n,k -> let f x y = *)
(*        ListSet.union (add_to_list_set x (generate_partitions (n-x) (k-1))) *)
(*          y *)
(*      in *)
(*      List.fold_right f (generate_int_list n) ListSet.empty *)


(* let () = *)

(*   let bounds =  *)
(*     NameMap.add "s1" (true, 3) (NameMap.add "s2" (true, 2) NameMap.empty) *)
(*   in *)
(*   let primary_signatures = ["s1"; "s2"] *)
(*   in *)
(*   let sigorder = *)
(*     (NameMap.add "s1" (NameSet.empty, false) *)
(*      (NameMap.add "s2" (NameSet.empty, false) NameMap.empty), *)
(*      EqClasses.singleton (NameSet.add "s1" (NameSet.singleton "s2")) *)
(*     ) *)
(*   in *)
(*  let sigenv = *)
(*     { sigord = sigorder; *)
(*       sigbounds = bounds; *)
(*     } *)
(*   in *)

(*   print_string "Traduction en LTL de phi2'\n"; *)
(*   let prof1 =  *)
(*     Profile.Union.add ["s1"; "s1"] (Profile.Union.singleton ["s2"; "s2"])  *)
(*   in *)

(*   let prof2 = *)
(*     let open Profile.Union in *)
(*     singleton ["s2";"s2"] *)
(*   in *)
(*   let t1 = { *)
(*     term = TConstRel "P"; *)
(*     profile = prof1 ; *)
(*   }        *)
(*   in *)
(*   let t2 = {  *)
(*     term = TConstRel "Q"; *)
(*     profile = prof2 ; *)
(*   } *)
(*   in *)
(*   let trans_t1 = { *)
(*     term = TUnop (Trans, t1); *)
(*     profile = prof1; *)
(*   } *)
(*   in *)
(*   let trans_t2 = { *)
(*     term = TUnop (Trans, t2); *)
(*     profile = prof2; *)
(*   } *)
(*   in *)
(*   let phi1 = K1.In (t1, trans_t2) in *)
(*   let phi2 = K1_to_k2.translate sigenv phi1 in *)

(*   print_ltl_formula @@ *)
(*     k2_to_ltl NameMap.empty sigenv phi2 *)


(* let () = *)

(*  let bounds = *)
(*     NameMap.add "s1" (true, 3) (NameMap.add "s2" (true, 2) NameMap.empty) *)
(*   in *)
(*   let primary_signatures = ["s1"; "s2"] *)
(*   in *)
(*   let sigorder = *)
(*     (NameMap.add "s1" (NameSet.empty, false) *)
(*      (NameMap.add "s2" (NameSet.empty, false) *)
(*             (NameMap.add "s11" *)
(*              (NameSet.singleton "s1", false) *)
(*              NameMap.empty)), *)
(*      EqClasses.singleton (NameSet.add "s1" (NameSet.singleton "s2")) *)
(*     ) *)
(*   in *)
(*  let sigenv = *)
(*     { sigord = sigorder; *)
(*       sigbounds = bounds; *)
(*     } *)
(*   in *)

(*   let f1_k2 =  *)
(*     Forall2 ("x", "s11", *)
(*        Forall2("y", "s2" , *)
(*          ConstPred2(Pred.make "P" *)
(*             (Profile.Union.add *)
(*                ["s1"; "s2"] *)
(*                Profile.Union.empty), *)
(*         ["x" ; "y"]))) *)
(*   in *)
(*   let f1_ltl= k2_to_ltl NameMap.empty sigenv f1_k2 in *)
(*   print_endline "First K2 formula:"; *)
(*   print_endline (K2PPrint.k2prop_to_string f1_k2); *)
(*   print_endline "First ltl formula:"; *)
(*   print_ltl_formula f1_ltl ; *)

(*   let f2_k2 = *)
(*     Forall2 ("x", "s1", *)
(*        Exists2("y", "s2" , *)
(*          ConstPred2(Pred.make "P" *)
(*             (Profile.Union.add *)
(*                ["s1"; "s2"] *)
(*                Profile.Union.empty), *)
(* ["x" ; "y"]))) *)
(*   in *)
(*   let f2_ltl =k2_to_ltl NameMap.empty sigenv f2_k2 in *)
(*   print_endline "Second K2 formula:"; *)
(*   print_endline (K2PPrint.k2prop_to_string f2_k2); *)
(*   print_endline "Second LTL formula:"; *)
(*   print_ltl_formula f2_ltl ; *)

(*   print_string "fin deuxieme formule\n\n"; *)




(*let () = print_string "p"*)

