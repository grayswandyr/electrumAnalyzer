(*****************************************************************************
 * Time-stamp: <2015-10-16 CEST 15:45:43 David Chemouil>
 *
 * Electrum Analyzer 
 * Copyright (C) 2014-2015 Onera
 * Authors: 
 *   David Chemouil 
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
 ****************************************************************************)

(*****************************************************************************
 * electrum_to_smv.ml - generation chain AST -> K1 -> K2 -> LTL -> SMV file
 ****************************************************************************)

open Batteries
open Util
open Elecfile_to_k1
open Elec_to_k1
open Profile


(* Produces smv files from an environment env of type Typing.envir_sig. 
*)
let execute verbosity outfile env =
  let (phi_model, phi_typ, locfacts, newenv) = env_to_phimodel env in
  let k1_static_facts, k1_dyn_facts = facts_from_env env in
  let k1_facts = K1.and1 (k1_dyn_facts, locfacts) in

  let open K1_pretty in
  let phi_string = string_of_prop phi_model in
  let phi_st_typ = string_of_prop phi_typ in
  if verbosity >= 1 then 
    begin
      Printf.printf "\n*** [K1] Phi Model ***\n%s\n" phi_string;
      Printf.printf "\n*** [K1] Phi typing ***\n%s\n" phi_st_typ;
      Printf.printf "\n*** [K1] Phi static facts ***\n%s\n" 
                    (string_of_prop k1_static_facts);
      Printf.printf "\n*** [K1] Phi non static facts ***\n%s\n" 
                    (string_of_prop k1_dyn_facts);
      Printf.printf "\n*** [K1] Phi local facts ***\n%s\n" 
                    (string_of_prop locfacts);
      Printf.printf "%s" (string_asserts env)
    end;
  
  let sigord = Elec_to_k1.(newenv.sigtot) in  
  let siglist = List.of_enum (NameMap.keys (fst sigord)) in
  let sigmult = sigmult_from_env env (fst sigord) in

  let abstract_sigs = abstract_sigs_from_env env siglist in

  (* compute the two formulas to send to NuXMV : 
     the invariant invar and the formula to check as an LTLSPEC *)  
  (* cmd = true => check, cmd = false => run *)
  let smv_formula_from_cmd is_check cmdnum formula bnd  =
    let sigenv = { 
      sigord = sigord; 
      sigbounds = bnd;
      sigmult = sigmult;
        abstract_sigs = abstract_sigs;
    } in
    Cfg.print_debug @@
      (string_of_int @@ NameMap.cardinal (fst sigenv.sigord))
      ^ " entries in sigord\n and "
      ^(string_of_int @@ NameMap.cardinal sigenv.sigmult)
      ^ " entries in sigmult\n";
        
    (* producing K2 *)
    let open K1_to_k2 in
    let k2_model, tc_set_model = 
      translate_with_tc_term_set sigenv phi_model in
    let k2_typing, tc_set_typing = 
      translate_with_tc_term_set ~typing:true sigenv phi_typ in
    let k2_fact, tc_set_fact = 
      translate_with_tc_term_set sigenv k1_facts in
    let k2_static_fact, tc_set_static_fact =
      translate_with_tc_term_set sigenv k1_static_facts in
    let k2_check_run, tc_set_check_run = 
      translate_with_tc_term_set sigenv formula in
    let k2_tc_set = 
      tcformula_from_term_set 
        sigenv 
        K1.(TermSet.union tc_set_static_fact 
              (TermSet.union tc_set_typing 
                 (TermSet.union tc_set_fact tc_set_check_run)))
    in

    (* producing LTL *)
    let open K2_to_ltl in
    let ltl_model = translate sigenv k2_model in
    let ltl_fact =  translate sigenv k2_fact in
    let ltl_static_fact = translate sigenv k2_static_fact in
    let ltl_check_run =
      translate sigenv k2_check_run in
    let inst_constraints = compute_instances_constraints sigenv in
    let ltl_tc_set = translate sigenv k2_tc_set in
    let ltl_typing = translate sigenv k2_typing in

    let open Ltl in
    let ltl_invar =
      ltland (ltl_static_fact,
              (ltland (ltl_model, 
                       ltland (inst_constraints, 
                               ltland (ltl_typing, ltl_tc_set)))))
    in
    let ltl_spec, cmdname =
      if is_check then
        (Ltl.limpl (ltl_fact, ltl_check_run), "check")
      else
        (Ltl.limpl (ltl_fact, Ltl.ltlnot ltl_check_run), "run")
    in
    if verbosity >= 1 then 
      begin
        let open Printf in
        printf "\n*** Bounds: ***\n"; print_bound bnd;

        printf "\n*** [K2] Model ***\n%s\n%!"
          (K2PPrint.k2prop_to_string k2_model);
        printf "\n*** [K2] typing ***\n%s\n%!"
          (K2PPrint.k2prop_to_string k2_typing);
        printf "\n*** [K2] static facts ***\n%s\n%!"
          (K2PPrint.k2prop_to_string k2_static_fact);
        printf "\n*** [K2] non static facts ***\n%s\n%!"
          (K2PPrint.k2prop_to_string k2_fact);
        printf "\n*** [K1] check/run formula:\n%s\n%!" 
          (string_of_prop formula) ;
        printf "\n*** [K2] check/run formula:\n%s\n%!"
          (K2PPrint.k2prop_to_string k2_check_run);

        printf "\n*** [LTL] instance constraints:\n%s\n%!"
          (Ltl_to_smv.ltl_to_string inst_constraints);
        printf "\n*** [LTL] Model ***\n%s\n%!"
          (Ltl_to_smv.ltl_to_string ltl_model);
        printf "\n*** [LTL] Facts ***\n%s\n%!"
          (Ltl_to_smv.ltl_to_string ltl_fact);
        printf "\n*** [LTL] Typing ***\n%s\n%!"
          (Ltl_to_smv.ltl_to_string ltl_typing);


        printf "\n*** [LTL] check/run formula:\n%s\n"
          (Ltl_to_smv.ltl_to_string ltl_check_run);
        Cfg.print_debug @@
        sprintf "\n*** [K2] transitive closure formula ***\n%s\n%!"
          (K2PPrint.k2prop_to_string k2_tc_set);
        Cfg.print_debug @@
        sprintf "\n*** [LTL] transitive closure formula ***\n%s\n%!"
          (Ltl_to_smv.ltl_to_string ltl_tc_set);
        printf "\n*** [LTL] invar formula:\n%s\n"
          (Ltl_to_smv.ltl_to_string ltl_invar)
      end;
    (* (ltl_invar, ltl_spec) *)
    let filename = Printf.sprintf "%s_%s_%03d.smv" outfile cmdname cmdnum in
    Printf.printf "Generating file: %s ... %!" filename; 
    Ltl_to_smv.to_nusmv ~invar:ltl_invar ltl_spec filename;
    print_endline "OK"
  in

  let generate is_check formulas_and_bounds = 
    List.iteri
      (fun cmdnum (fml, bnd) -> smv_formula_from_cmd is_check (cmdnum + 1) fml bnd)
      formulas_and_bounds
  in
  generate true @@ list_of_check_formulas_and_bounds env sigord sigmult abstract_sigs;
  generate false @@ list_of_run_formulas_and_bounds env sigord sigmult abstract_sigs
  
