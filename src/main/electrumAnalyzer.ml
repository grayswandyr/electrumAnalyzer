(*****************************************************************************
 * Time-stamp: <2015-10-29 CET 09:41:27 David Chemouil>
 *
 * Electrum Analyzer 
 * Copyright (C) 2014-2015 Onera; (C) 2015 IRIT
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
 * electrumAnalyzer.ml - contains the "main" for the Electrum Analyzer.
 ****************************************************************************)

open Batteries
open Util
open Faulty
open Cmdliner
open Typing

open Elecfile_to_k1
(*open K1_to_k2 *)
open K1
open K2
(* open K2_to_ltl *)
open PPrint
open Elec_to_k1
open K1_pretty
open Profile


(* This function is only used for tests and debugs *)
let test_translations x =
  let (phi_model,phi_typ,locfacts, newenv) = env_to_phimodel x in
  let k1_static_facts, k1_dyn_facts = facts_from_env x in
  let k1_facts = K1.and1(k1_dyn_facts,locfacts) in
  let phi_string = string_of_prop phi_model in
  let phi_st_typ = string_of_prop phi_typ in
  Cfg.print_debug @@ Printf.sprintf "\n*** Phi Model ***\n%s\n" phi_string;
  Cfg.print_debug @@ Printf.sprintf "\n*** Phi typing ***\n%s\n" phi_st_typ;
  Cfg.print_debug @@ Printf.sprintf "%s" (string_asserts x);

  let sigord = newenv.sigtot in
  let sigmult = sigmult_from_env x (fst sigord) in

  let siglist = (List.of_enum (NameMap.keys (fst sigord))) |> 
                List.filter 
                  (fun s-> is_primary2 sigord s && s <> Names.univ 
                           && s <> Names.empty) 
  in
  let bnds = default_bounds sigmult siglist in
  let mult_of_sigs = sigmult_from_env x (fst sigord) in
  let abstr_sigs = 
    abstract_sigs_from_env x  
      (List.of_enum (NameMap.keys (fst sigord))) 
  in
  let min_instances_set_map = min_instances_map_from_env sigord sigmult in

  let inst_set_map =
    compute_atoms_per_sig sigord bnds sigmult min_instances_set_map abstr_sigs
  in
  let sigenv =
    { sigord = sigord;
      sigbounds = bnds;
      sigmult = mult_of_sigs;
      abstract_sigs = abstr_sigs;
      lowerbounds = min_instances_set_map;
      instances_map = inst_set_map;
    }
  in
  let k2_model = K1_to_k2.translate sigenv phi_model in
  let k2_fact = K1_to_k2.translate sigenv k1_facts in
  let k2_static_fact = K1_to_k2.translate sigenv k1_static_facts in
  let k2_model_fact = K2.and2(k2_model, k2_fact) in
  let k2_typing = K1_to_k2.translate ~typing:true sigenv phi_typ in
  Cfg.print_debug @@ Printf.sprintf "\n*** K2 Model ***\n%s\n"
                       (K2PPrint.k2prop_to_string k2_model);
  Cfg.print_debug @@ Printf.sprintf "\n*** K2 typing ***\n%s\n"
                       (K2PPrint.k2prop_to_string k2_typing);
  Cfg.print_debug @@ Printf.sprintf "\n*** K2 Facts ***\n%s\n"
                       (K2PPrint.k2prop_to_string k2_fact);
  Cfg.print_debug @@ Printf.sprintf "\n*** K2 Facts ***\n%s\n"
                       (K2PPrint.k2prop_to_string k2_static_fact);                      
  let ltl_model = K2_to_ltl.translate sigenv k2_model_fact in
  Cfg.print_debug @@ Printf.sprintf "\nLTL model:\n%s\n"
                       (Ltl_to_smv.ltl_to_string ltl_model);
  let ltl_typing = K2_to_ltl.translate sigenv k2_typing in
  Cfg.print_debug @@ Printf.sprintf "\nLTL typing :\n%s\n"
                       (Ltl_to_smv.ltl_to_string ltl_typing);
  let inst_constraints =
    K2_to_ltl.compute_instances_constraints sigenv
  in
  Cfg.print_debug @@ Printf.sprintf "\n*** [LTL] instance constraints:\n%s\n"
                       (Ltl_to_smv.ltl_to_string inst_constraints)



let run verbosity prettyprint inclpath infile outfile =
  try
    if verbosity >= 2 then
      begin
        Cfg.debug := true;
        Printexc.record_backtrace true
      end;
    (* remove duplicates *)
    Cfg.alloyfolder := inclpath ^ "/";

    Printf.printf
      "%s %s (%s).\n\
       (C) 2014-2015 Onera, (C) 2015 IRIT.\n\
       Released under the GNU GPL 3.0 or later WITHOUT ANY WARRANTY.\n\
       The %s relies on third-party free software.\n\
       Please use the --help option for more information.\n%!"
      Cfg.app_name 
      Build.version
      Build.timestamp
      Cfg.app_name;

    (* redefine outfile *)
    let genfile =
      if outfile = "" then
        let open Filename in
        let noext = try chop_extension infile with Invalid_argument _ -> infile in
        basename noext 
      else 
        outfile
    in

    let ast = Parser_main.parse infile in

    let env =
      handle
        ~f:(fun ast ->
             if prettyprint then Pretty.print ast;
             process_root ast
           ) ast
        ~handle:(function `ESyntax | `ELexing -> (fun msg->
              failwith @@ Printf.sprintf "Parsing Error: %s" msg))
    in
    handle ~f:(fun env ->
          if verbosity > 0 then print_endline (envirsig_to_string env);
          Electrum_to_smv.execute verbosity genfile env;
          let secs = Sys.time () in
          let intsecs = int_of_float secs in
          let m = intsecs / 60 in
          let rem = secs -. 60. *. float_of_int m in
          Printf.printf "Done (%dm%3Fs).\n%!" m rem
        ) env
      ~handle:(function `ETyping ->    
            Printf.eprintf "ERROR: Typing (%s): %s\n%!" infile)
  with
    | Invalid_argument s -> Printf.eprintf "ERROR: Invalid argument: %s\n%!" s
    | Failure s ->  Printf.eprintf "ERROR: Failure: %s\n%!" s


(* Commandline management *)

let verbose =
  let doc = "Verbosity level (0 = nominal, 1 = +show types, \
             2 = +show debugging information)." in
  Arg.(value & opt int 0 & info ["v"; "verbosity"] ~docv:"LEVEL" ~doc)

let infile =
  let doc = "File to process." in
  Arg.(required & pos 0 (some non_dir_file) None & info [] ~docv:"FILE" ~doc)

let pp =
  let doc = "Pretty-print the model." in
  Arg.(value & flag & info ["pp"; "pretty"] ~doc)

let inclpath =
  let default = "./examples/alloy/" in
  let doc = Printf.sprintf "Directory for imported modules (default: \"%s\")." default in
  Arg.(value & opt dir default & info ["I"] ~docv:"DIRECTORY" ~doc)

let outfile =
  let doc = "Pattern for the names of the SMV files to generate \
             (absent: generate in the current directory \n\
             using as pattern the base name of the input file)." in
  Arg.(value & opt string "" & info ["o"; "output"] ~docv:"STRING" ~doc)

let main_term = Term.(pure run $ verbose $ pp $ inclpath $ infile $ outfile)

let third_party_blurb = {| 
                           The Electrum Analyzer relies on the following third-party free software, released
                           under their respective licence (shown below; see the respective OPAM
                           repositories for the full text of the licences):
                           - pprint: CeCILL-C;
                           - menhir generator: Q Public License v1.0 + special exception;
                           - menhirLib: GNU LGPL v2 + special exception;
                           - batteries: GNU LGPL v2.1;
                           - cmdliner: BSD3.
                        |}

let author_blurb = {|
Julien Brunel, David Chemouil, Denis Kuperberg.
|}

let main_info =
  let doc = "formal verification of Electrum models" in
  let man = [ `S "ISSUES";
              `P "Report issues at \
                  <https://forge.onera.fr/projects/electrum/issues/new>.";
              `S "COPYRIGHT";
              `P "Electrum Analyzer (C) 2014-2015 Onera, (C) 2015 IRIT";
              `P "The Electrum Analyzer is free software: you can redistribute \
                  it and/or modify it under the terms of the GNU General \
                  Public License as published by the Free Software Foundation, \
                  either version 3 of the License, or (at your option) any \
                  later version.";
              `P "The Electrum Analyzer is distributed in the hope that it \
                  will be useful, but WITHOUT ANY WARRANTY; without even the \
                  implied warranty of MERCHANTABILITY or FITNESS FOR A \
                  PARTICULAR PURPOSE.  See the GNU General Public License for \
                  more details.";
              `P "You should have received a copy of the GNU General Public \
                  License along with the Electrum Analyzer.  If not, see \
                  <http://www.gnu.org/licenses/>.";
              `S "THIRD-PARTY SOFTWARE";
              `P third_party_blurb;
              `S "AUTHORS";
              `P author_blurb
            ] in
  Term.info Sys.argv.(0) ~version:Build.version ~doc ~man

let () = match Term.eval ~argv:(Sys.argv) (main_term, main_info) with
  | `Error _ -> exit 1
  | _ -> exit 0

