(*******************************************************************************
 * Time-stamp: <2016-03-02 CET 11:42:51 David Chemouil>
 * 
 * Electrum Analyzer 
 * Copyright (C) 2014-2015 Onera, (C) 2015 IRIT
 * Authors: 
 *   Denis Kuperberg 
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
 ******************************************************************************)

open Batteries
open K1
open Elec_to_k1
open Profile
open Ast_expr
open Ast_par
open Ast_ctrl
open Types
open Typing
open Fresh
(*

   We assume that the typing function deals with file inclusions etc, 
   and returns a better format: list of sigs, asserts, facts, commands 

*)

(* phi_typage for rel has profile *)
(* let typ_term rel prof name_var= *)
(*   (\* group the ranges by arity size *\) *)
(*   let arunion=group_arities prof in *)
(*   (\* treat only one size: *)
(*      forall x1,... xk in globterm, *)
(*      Or_{vec A in setk}, And_i x_i in A_i *)
(*         *\) *)
(*   let onearity setk = *)
(*     let vars = List.map (fun _ -> Fresh.fresh name_var) (Union.choose setk) in *)
(*     let varterms = *)
(*       List.map *)
(*         (fun v-> { term = TVar v; *)
(*                    profile = Profile.Union.singleton [ Names.univ ] }) vars in *)
(*     let treatrange l= *)
(*       conjlist (List.map2 *)
(*                   (fun v s-> K1.In (v,sig_term s)) varterms l) *)
(*     in *)
(*     let goodtypes=Union.fold *)
(*                     (fun l acc -> or1(treatrange l, acc)) *)
(*                     setk False in *)
(*     (\*product of variables *\) *)
(*     let varprod=List.fold_left (fun accvars v-> *)
(*           prod_term accvars v) *)
(*           (List.hd varterms) (List.tl varterms) *)
(*     in *)
(*     let phi_imp=impl1 (K1.In (varprod,rel), goodtypes) *)
(*     in *)
(*     List.fold_right (fun h res -> forall1 ([h], univ_term, res)) vars phi_imp *)
(*   in *)
(*   ArUnion.fold (fun setk bigacc -> and1(onearity setk, bigacc)) arunion True *)

(* Yields the typing formula for a relation 'rel' in range 'rangeterm'. *)
(* To avoid quantifying on univ^k (and reduce the state space when instantiating
   to LTL), we quantify on the primary sig of every signature of every range of
   the profile of 'rel'. *)
(* CAUTION: this works because we rely on the fact that the typechecker
   rejects trivially empty expressions, i.e. where an expression would involve a
   variable not in this primary signature and composed with 'rel' in one way or
   another. Besides overloading is not handled in typechecking yet. *)
(* CAUTION2: We actually don't quantify explictly but build an inclusion
   formula. This works because LTL generation does not take into account the
   profile of a relation (even after it has been translated to a predicate). If
   this changes, then the following translation will be erroneous and an
   explicit formula will be necessary.*)
(* last arg: a base name for fresh variable if we quantify, ignored for now (see
   above why) *)
   (*
   let typ_term order rel rangeterm _ =
   let this_sig = List.hd @@ Union.choose rel.profile in
   let this_sig_term = K1.sig_term this_sig in
   (* build 'rel' with profile changed to primary sigs (see above) *)
   let rel_prim =
   { rel
   with profile =
   Union.map (List.map (primary_sig_of2 order))
   rel.profile } in
   (* forall x: A | x.field in x.range 
   let freshrel= fresh_of_term rel_this *)
   let res = K1.In (rel_prim, K1.prod_term this_sig_term rangeterm) in
   Cfg.print_debug
   @@ Printf.sprintf "Elecfile_to_k1.typ_term: yielding %s with profile %s: %s\n%!"
   (K1_pretty.string_of_prop res)
   (K1_pretty.string_of_term rel_prim)       
   (Profile.Union.to_string rel_prim.profile);
   res
*)



(* local fields of sig : produces a NameSet of the fields of a signature,
   including from the parents *)
let localfields sig_name envalias=
  (* NameSet of fields of a signature *)
  let fields_of_sig s=
    List.fold_left (fun accset (decl:Ast_expr.decl)-> 
          let fnames=List.map id_to_name decl.names
          in NameSet.union (NameSet.of_list fnames) accset)
      NameSet.empty s.fields 
  in  
  (* find the signature associated to a name, and compute its fields *)
  let fields_of_name sname = 
    let (_,sigres)=try List.find (fun (l,s) -> 
          List.exists (fun qname-> qn_to_name qname=sname) l)
          envalias.sigs
      with Not_found -> failwith ("Signature Name: "^sname^"
              not appearing in signature list")
    in fields_of_sig sigres
  in
  (* signature names extending s *)
  let (sig_namemap,_)=envalias.sigtot in
  let (larger_signames,_) = NameMap.find sig_name sig_namemap in
  (* merge all of them *)
  NameSet.fold 
    (fun sname accset -> NameSet.union (fields_of_name sname) accset)
    larger_signames
    (fields_of_name sig_name)


(* from a name to its profile using a map of names to bt *)
(* let name_to_bt name assocnames=
   try NameMap.find name assocnames with
   Not_found -> failwith ("Unkwnown Name: "^name^"
   in the environment") *)

(* returns expression where each local field r of sig
   is replaced by This.r 
*)
let globalexpr expression signame envalias=
  (* the set of fields to update *)
  let fieldset = localfields signame envalias in
  (* replace one field r in t by this.r *)
  let replfield expr r=
    (* Warning: ugly fix :
       get the path by retrieving it from the signature name, using the last / *)
    let r_qname= name_to_qn_path r signame in 
    let bt= try mapfind r_qname envalias.assoc with
        Not_found -> failwith ("Field "^r^" of signature "^signame^" not found in environment")
    in
    let sig_qname=name_to_qn signame in
    let (_,sig_variable)= try mapfind sig_qname envalias.sigord with
        Not_found -> failwith ("Signature "^signame^" not found in environment")
    in
    let bt_sig=sigtype sig_qname sig_variable in
    let rvar = {expr with (*just to have a location *)
                  expr=EQualName r_qname;
                  typ = Some bt;} in
    let ethis={rvar with
                 expr=EThis;
                 typ= Some bt_sig;} in
    let newr=EBinary (ethis, BDot, rvar)
    in rep_expr r_qname newr expr
  in
  NameSet.fold (fun r accexpr -> replfield accexpr r) fieldset expression

(* generates the formula : forall x:sig | x.field in range (updated with x.localfields) 
   also (sigprim-sig).r=emptyset, if sig not primary

   also deals with disjoint_ranges, i.e. generates the formula
   "forall a,b:sig | a!=b => no a.field & b.field" if inject_bool is true
*)
let typ_term envalias (globterm,cont_term) range signame inject_bool=
  let sigterm = sig_term signame in
  (* the new x *)
  let freshvar= fresh_of_term sigterm   in
  let freshterm = {sigterm with term=TVar freshvar;} in
  let termfield={cont_term with
                   term=TBinop(Join, freshterm, globterm);} in
  (* add "this." in front of local fields *)
  let newrange = globalexpr range signame envalias in
  let envthis={envalias with
                 curthis = Some freshterm; (* replace 'This' with the fresh variable *)
                 curterm = Some termfield;
                 rootmult=true;
                 local_names=[];
              } in
  let (termrange, _ )=expr_to_k1term newrange envthis in
  let propincl= K1.In (termfield, termrange) in
  let forallprop=forall1([freshvar], sigterm, propincl) in

  let forallinj= match inject_bool with
    | false -> forallprop
    | true -> 
        let injective= (* forall a,b:sig | a!=b => no a.field & b.field *)
          let a= fresh_of_term sigterm   in
          let b= fresh_of_term sigterm   in
          let aterm = {sigterm with term=TVar a;} in
          let bterm = {sigterm with term=TVar b;} in
          let afield={cont_term with
                        term=TBinop(Join, aterm, globterm);} in
          let bfield={cont_term with
                        term=TBinop(Join, bterm, globterm);} in
          let interm={afield with term= TBinop(Inter,afield,bfield)} in
          let propdisj=Equal(interm, empty_term) in
          let propinj= impl1(not1 (Equal(aterm,bterm)), propdisj) in
          forall1([a],sigterm,forall1([b],sigterm,propinj))
        in and1(forallprop,injective)
  in
  (* add (sigprim-sig).r=emptyset, if sig not primary *)
  if is_primary2 envalias.sigtot signame 
  then forallinj
  else
    let sigprim=primary_sig_of2 envalias.sigtot signame in
    let primterm=sig_term sigprim in
    let diffterm={primterm with
                    term=TBinop(Diff, primterm, sigterm);} in
    let jointerm={termfield with 
                    term= match termfield.term with
                      |TBinop(Join, _ , globterm) ->TBinop(Join, diffterm , globterm)
                      | _ -> assert false;} in
    let emptyprop= K1.Equal (jointerm, empty_term)
    in and1(forallinj, emptyprop)


(* treat one signature name: fields and multiplicity *)
let onesig_to_k1prop signature signame envalias=
  let open Ast_expr in
  let sigterm=sig_term signame in 
  (* list of field qnames for dereferencing *)
  let field_names= 
    let setfields = localfields signame envalias
    in List.map name_to_qn (NameSet.to_list setfields)
  in
  (* from a declaration to a (term, phi_model, phi_typage) *)
  let treat_decl d=
    let treatident id =
      let rawterm = if d.is_variable 
        then TVarRel (id_to_name id)
        else TConstRel (id_to_name id)
      in
      let locprof = e_to_prof d.range in
      (* debug *)
      (*Printf.printf
        "Profile of %s is %s\n"
        (Util.PPrintX.to_string @@ Pretty.expr_to_document d.range)
        (Union.to_string locprof);*)

      (* put in context of the signature *)
      let globprof= prof_prod sigterm.profile locprof in
      let globterm={term=rawterm; profile=globprof} in


      (*  signature in context, quantified universally *)
      let sigvar=fresh_of_term sigterm in
      let varterm={sigterm with term=TVar sigvar} in
      let cont_term={
        term=TBinop(Join, varterm, globterm);
        profile=locprof}
      in


      (* doing the conversion with all necessary context *)
      let envcont={envalias with
                     curterm=Some cont_term;
                     curthis=Some sigterm;
                     rootmult = true;
                     local_names=field_names;
                  } 
      in
      let (rangeterm,flist)=
        expr_to_k1term d.range envcont
      in
      let phi_const=forall1([sigvar], sigterm, conjlist flist) in

      (* forall x:sig | x.field in x.range where appropriate ! *)
      let typform= 
        typ_term envalias (globterm,cont_term) d.range signame d.is_disjoint_ranges
      in 
      (globterm, phi_const,typform)

    in 
    (*treat all identifiers of the declaration *)
    let (termlist, phi_mod,phi_typ)=List.fold_left 
                                      (fun (acc1,acc2,acc3) id -> let (x,y,z) = treatident id in
                                        x::acc1, and1(y,acc2), and1(z,acc3) ) ([],True,True) d.names
    in
    let phi_model=
      if d.is_disjoint_variables then 
        let disjform = 
          let rec treat x l=
            match l with 
              |[] -> True
              |y::[] ->  not1 (Equal (x,y))
              |y::q -> let frec = and1(treat x q, treat y q) in
                  and1(not1 (Equal (x,y)),frec)
          in match termlist with
            |[] -> failwith "empty declaration"
            |x::q -> treat x q
        in and1(disjform, phi_mod)
      else phi_mod
    in 
    (phi_model, phi_typ)
  in (* now treat all declarations *)
  let (psi_mod,psi_typ)=List.fold_left (fun (acc1,acc2) decl -> 
        let (phi1,phi2)=treat_decl decl in
        (and1(phi1,acc1), and1 (phi2,acc2))
      )
        (True, True)
        signature.fields
  in
  (* multiplicity *)
  let psi_mod2=match signature.mult with
    | None -> psi_mod
    | Some m ->
        let x=fresh_of_term sigterm in
        let y=fresh_of_term sigterm in
        let xterm={term=TVar x; profile=sort_prof signame} in
        let yterm={term=TVar y; profile=sort_prof signame} in
        let phi_some=exists1([x], sigterm, True) in
        let phi_lone=forall1([x],sigterm,
                             forall1([y], sigterm, Equal(xterm, yterm))) in
        let phi_one = exists1([x], sigterm, 
                              (forall1 ([y],sigterm, Equal(xterm, yterm)))) in
        let multform = 
          match m with
            |`Some ->  phi_some
            |`Lone -> phi_lone
            |`One -> phi_one
        in
        and1 (psi_mod,multform)
  in 
  (* optional local fact *)
  let psi_locfact=match signature.fact with
    |None -> True
    |Some bloc ->
        let factlist=List.map (fun e->
              (* forall var_s:sig | fact[local_r<-this.local_r] *)
              let var_s= fresh_of_term sigterm in
              let term_s= {sigterm with term=TVar var_s} in
              let cond=expr_to_k1prop e 
                         {envalias with 
                            curthis=Some term_s;
                            curterm=None;
                            local_names=field_names;
                         }
              in Always (forall1([var_s],sigterm, cond))
            ) bloc
        in  
        conjlist factlist
  in (psi_mod2, psi_typ,psi_locfact)





(* treat the whole signature declaration, with several names
   'abstract', 'extends' will need to be treated globally
*)
(* returns (phi_mod, phi_typ) *)
let sig_to_k1prop envalias (qnamelist, signature) =
  let namelist= List.map qn_to_name qnamelist in
  (* main formula with fields *)
  List.fold_left
    (fun (acc1,acc2,acc3) n->let (a,b,c)=onesig_to_k1prop signature n envalias
      in (and1(a,acc1),and1(b,acc2),and1(c,acc3)))
    (True,True,True)
    namelist

(* 
   deals with all signature simultaneously
   necessary to treat extensions and abstract signatures 

   before calling it, be sure that the qnames and ids are coherent,
   and can safely be turned to simple names
   Also, preprocess the signature list to include a field "exists" for variable signatures 

*)

let sigs_to_k1prop siglist envalias=
  (* formula with all fields etc*)
  let (phi_mod, phi_typ,psi_locfact)=
    List.fold_left
      (fun (acc1,acc2,acc3) qns_sig -> let (a,b,c)=sig_to_k1prop envalias qns_sig
        in (and1(a,acc1),and1(b,acc2),and1(c,acc3)))
      (True,True,True)
      siglist
  in

  (* inclusions *)
  let incl_one accphi (qnamelist, signature)=
    let namelist= List.map qn_to_name qnamelist in
    let phi_in_list smallsig =
      let smallterm=sig_term smallsig in
      (match signature.extends with
        |None -> True
        |Some (In qn_list) -> 
            (* forall x in sig, x in A1 or x in A2 or ...*)
            let x=fresh_of_term smallterm in
            let xterm={smallterm with term= TVar x} in
            let disjx=
              List.fold_left
                (fun accdisj qn-> 
                   let bigt=sig_term (qn_to_name qn) in
                   or1(accdisj, K1.In(xterm, bigt)))
                False
                qn_list
            in forall1([x],smallterm, disjx)
        |Some (Extends qn) -> 
            (* just smallsig in qn *)
            let bigt=sig_term (qn_to_name qn) in
            K1.In(smallterm, bigt)
      )
    in 
    let ins = conjlist (List.map 
                          (fun st-> phi_in_list st) namelist) 
    in
    and1(accphi,ins)

  in
  let incls= List.fold_left incl_one True siglist in


  (* constraints from abstract, extends *)
  let terms_ext signame=
    (* list of signatures that extend this one *)
    let ext_list= List.filter 
                    (fun (qnamelist,s) -> match s.extends with
                       |Some (Extends qn) -> qn_to_name qn=signame
                       | _ -> false)
                    siglist 
    in
    (* flatten the list and turn it to terms *)
    let termlist=List.fold_left (fun acc (qnamelist,s) -> 
          let terms=List.map (fun qn-> sig_term (qn_to_name qn)) qnamelist
          in acc@terms) [] ext_list
    in  
    (*also turn the list into a set for signame_order *)
    (* this is the eqclass relative to signame *)
    let eqclass=
      List.fold_left (fun accset (qnamelist,s) -> 
            let newset=NameSet.of_list (List.map qn_to_name qnamelist) 
            in NameSet.union accset newset) NameSet.empty ext_list
    in (termlist, eqclass)  
  in



  (* returns a formula for disjonction/partition for only one name *)


  (* auxiliary function returning (disjunction of terms, union term) *)
  let rec build reslist sigterm=
    match reslist with
      |[] -> True, empty_term
      |[t] -> True,t
      |[t1;t2] -> 
          let int_term={t1 with term=TBinop(Inter,t1,t2)} in
          let union_term={sigterm with term = TBinop(Union,t1,t2)} in
          Equal(int_term, empty_term), union_term
      |t::q -> 
          let phi_t= conjlist (
                List.map (fun x-> 
                      let int_term={t with term=TBinop(Inter,t,x)} in
                      (Equal(int_term, empty_term))
                    ) q) in
          let (phi_q, union_q)=build q sigterm in
          let union_term={sigterm with term = TBinop(Union,t,union_q)} in
          and1(phi_t,phi_q), union_term
  in

  let one_disjform signature sig_qn =
    let signame=qn_to_name sig_qn in
    let sigterm= sig_term signame in
    let (termlist,eqclass)=terms_ext signame in

    let (phi, union_t)=build termlist sigterm in
    let finalphi=if signature.is_abstract 
      then and1(phi, Equal(union_t, sigterm))
      else phi
    in (finalphi, eqclass)
  in
  (* treat signature declaration with multiple names *)
  let disjform (qnamelist,signature)=
    List.fold_left (fun (phi,classes) sig_qn->
          let (newphi, newclass)= one_disjform signature sig_qn
          in and1(phi,newphi), EqClasses.add newclass classes
        ) 
      (True, EqClasses.empty)
      qnamelist
  in


  (*
     let univsig=
     {is_variable =false;
     is_abstract = true;
     mult = None;
     names = [];
     extends = None;
     fields = [];
     fact = None;
     }
     in
  *)

  (* We add 'extend univ' when no In or Extend is mentioned 
     let univ_qn=Ast.Qname.local (Ast_ident.make Names.univ) in
     let update_ext (qnlist, signature)=
     if signature.extends = None
     then (qnlist,{signature with extends=Some (Extends univ_qn)})
     else (qnlist,signature)*)

  (* finally treat the list of all signatures *)
  let (constraints, eqclasses) = 
    List.fold_left (fun (phi,classes) qn_sig->
          let (newphi, newclasses)= disjform qn_sig
          in and1(phi,newphi), EqClasses.union newclasses classes
        ) 
      (incls, EqClasses.empty)
      siglist

  (* we add the 'toplevels extends univ' to constraints and Eqclasses *)
  in 
  let (signames, _)=envalias.sigtot 
  in
  let toplevel qname=
    let (set,var)=try NameMap.find (qn_to_name qname) signames
      with Not_found -> failwith ("Elecfile_to_k1: Sort "^(qn_to_name qname)^" not found\n")
    in NameSet.is_empty set
  in
  let topnames=List.fold_left 
                 (fun accset (qnlist,_)->
                    (List.map qn_to_name (List.filter toplevel qnlist))@accset
                 ) [] siglist
  in
  let topclass=NameSet.of_list topnames in
  let neweqclasses=EqClasses.add topclass eqclasses in
  let newconst=
    let topterms=List.map sig_term topnames in
    let (phi_disj,unionterm)= build topterms univ_term in
    and1(constraints, and1(phi_disj, Equal(unionterm, univ_term)))
  in
  (* add none and univ in the order *)
  let newsignames=
    let allnames=
      (* previously it was retrieved from siglist,
         code below in case we want it back:
         ----------------------
         List.fold_left 
         (fun accset (qnlist,_)->
         let newset =NameSet.of_list (List.map qn_to_name qnlist)
         in NameSet.union newset accset
         ) NameSet.empty siglist *) 
      NameSet.of_enum (NameMap.keys signames)

    in
    (*add none*)
    let mapnone=NameMap.add Names.empty (allnames,false) signames in
    (*add univ to everyone*)
    let mapnone2=
      let adduniv_one (set,var)= (NameSet.add Names.univ set,var) in
      NameMap.map adduniv_one mapnone
      (*add univ*)
    in NameMap.add Names.univ (NameSet.empty,false) mapnone2

  in  

  let finalphi_typ=
    (* the constraints must be true at all times *)
    (* always1(and1 (phi_typ, newconst)) *)
    (* alternative definition without always because finalphi_typ will be 
       considered as an invariant by NuSMV *)
    and1(phi_typ, newconst)

  in 
  (* we return the new environment with correct sigtot *)
  let newsigtot= (newsignames, neweqclasses) in
  (phi_mod,finalphi_typ, psi_locfact, {envalias with sigtot=newsigtot; curterm=None})

(* fact list to proposition, fact names are ignored for now *)
let facts_to_k1props factlist envalias_init=
  let envalias={envalias_init with curterm=None} in
  let treat_fact (f:fact)= conjunct f.body envalias
  in List.map treat_fact factlist

let facts_from_env env=
  let envalias=envir_to_aliases env in
  let facts = facts_to_k1props env.factlist envalias in
  let static_facts, dyn_facts = 
    List.partition (prop_is_trivial_invar envalias.sigtot) facts 
  in
  let new_static_facts = List.map remove_always_in_static_fact static_facts in
  conjlist new_static_facts , conjlist dyn_facts 


(* assert list 
   This time we retur a list of pairs (name option, formula)
*)
let asserts_to_props assertlist envalias=
  let treat_assert a= (a.name,conjunct a.body envalias)
  in List.map treat_assert assertlist


(* we can now compute phi_model from an environment *)
let env_to_phimodel env=
  let envalias=envir_to_aliases env in

  (* computing phi_model, phi_typ, newenv *)
  sigs_to_k1prop env.sig_list envalias

(* returns the commands of type check from an environment (of type envir_sig) *)
let search_check_commands env =
  let is_check cmd =
    match cmd with
      | NamedCmd (_, cmdtype, _, _) -> cmdtype = Check
      | BlockCmd (_, cmdtype, _, _ ) -> cmdtype = Check
  in
  List.filter is_check env.cmdlist

(* converts a (basic) bound type into a profile, i.e., it must correspond to a 
   single signature *)
let basic_bt_to_prof bt =
  let prof = bt_to_prof bt in
  if Union.cardinal prof = 1 && List.length (Union.choose prof) = 1
  then prof
  else
    failwith "elec_file_to_k1: cmd_to_prop: the profile of a predicate in a 
        run command must be basic"

(* returns bounds (of type typescopes) from a signame_order, a signame_mult 
   and a list of typescope 
   Reminder: type typescopes = (bool * int) NameMap.t
   type typescope = bool * int * Ast_qname.t
*)  
let bnds_from_scopes sigord sigmult abstr_sigs typescope_list =

  (* bounds for signatures given in the typescope list, i.e., in the command *)
  let bounds_from_ts_list =
    List.fold_right 
      (fun (x1, x2, x3) y -> 
         let signame = qn_to_name x3 in

         (* if the signature in the command does not exist in the electrum model
            then we print a warning
         *)
         if not (NameMap.mem signame sigmult)
         then
           begin
             if signame <> "Time"
             then
               print_endline ("WARNING : signature " 
                              ^ signame 
                              ^ " used in a command but not present in the model.");
             y
           end
         else
           (* if the signature signame is variable and primary (the only bigger 
              signature is the hull of signame) then the scope applies to the 
              hull of signame *)
           let greater_sigs, _ = 
             begin
               try
                 NameMap.find signame (fst sigord)  
               with 
                 | Not_found -> failwith ("Elecfile_to_k1.bnds_from_scopes: \ 
               signature "
                                          ^ signame ^ " not found.")
             end
           in
           let hull_name =  Ast_ident.to_string @@
             Ast.Hull.to_hull @@ Ast_ident.make signame
           in
           if NameSet.equal greater_sigs 
                (NameSet.add hull_name (NameSet.singleton Names.univ))
           || NameSet.equal greater_sigs (NameSet.singleton hull_name)
           then
             NameMap.add hull_name (x1,x2) y

           else
             (* if the signature is not primary then we print a warning, 
                because the bound is not taken into account 
             *)
           if not (is_primary2 sigord signame)
           then
             begin
               print_endline ("WARNING: A scope was given to signature " 
                              ^ signame
                              ^ " which is not primary. It will be ignored.");
               y
             end
           else
             let min_bnd = min_bound sigord sigmult abstr_sigs signame in
             let max_bnd = max_bound sigord sigmult abstr_sigs signame in
             if min_bnd > max_bnd && (max_bnd <> -1)
             then
               failwith ("Elecfile_to_k1.bnds_from_scopes: derived bounds for "
                         ^ signame ^ " are not coherent.\n" 
                         ^ "Min bound = " ^ (string_of_int min_bnd) 
                         ^ "\nMax bound = " ^ (string_of_int max_bnd))
             else
               (* if the multiplicity of a sig is completely determined by the 
                  model, then we force the bound to this value *)
             if min_bnd = max_bnd
             then
               NameMap.add signame (true, min_bnd) y 
             else
               (* if the required bound is greater than the maximum bound
                  then we force the bound to the maximum bound
               *)
             if x2 > max_bnd && (max_bnd <> -1)
             then
               NameMap.add signame (x1, max_bnd) y
             else
               (* if the required bound is lower than the minimum bound
                  then we force the bound to the minimum bound
               *)
             if x2 < min_bnd
             then
               NameMap.add signame (true, min_bnd) y
             else
               (* else we consider the scope given in the command *)
               NameMap.add signame (x1, x2) y
      )
      typescope_list 
      NameMap.empty
  in
  let prim_sigs = 
    BatSet.filter (is_primary2 sigord) 
      (BatSet.of_enum (NameMap.keys (fst sigord))) 
  in

  (* management of signatures for which no bound is given explicitely *)
  let rest = BatSet.diff prim_sigs 
               (BatSet.of_enum (NameMap.keys bounds_from_ts_list)) 
  in
  BatSet.fold 
    (fun x y -> 
       let min_bnd = min_bound sigord sigmult abstr_sigs x in
       let max_bnd = max_bound sigord sigmult abstr_sigs x in

       if min_bnd > max_bnd && (max_bnd <> -1)
       then
         failwith ("Elecfile_to_k1.bnds_from_scopes: derived bounds for "
                   ^ x ^ " are not coherent.")
       else
         (* if the multiplicity of a sig is completely determined by the 
            model, then we force the bound to this value *)
       if min_bnd = max_bnd
       then
         NameMap.add x (true, min_bnd) y
       else
         (* if 3 is greater than the maximum bound
            then we force the bound to the maximum bound
         *)
       if 3 > max_bnd && (max_bnd <> -1)
       then
         NameMap.add x (false, max_bnd) y
       else
         (* if 3 is lower than the minimum bound
            then we force the bound to the minimum bound
         *)
       if 3 < min_bnd
       then
         NameMap.add x (true, min_bnd) y
       else
         (* else we add the scope by default *)       
         NameMap.add x (false, 3) y
    )
    rest
    bounds_from_ts_list

(* idem as bnds_from_scopes but the default bound is given in parameter 
   instead of 3 
*)  
let bnds_from_scopes_but sigord sigmult abstr_sigs k typescope_list =
  (* bounds for signatures given in the typescope list, i.e., in the comand *)
  let bounds_from_ts_list =
    List.fold_right 
      (fun (x1, x2, x3) y -> 
         let signame = qn_to_name x3 in
         (* if the signature in the command does not exist in the electrum model
            then we print a warning
         *)
         if not (NameMap.mem signame sigmult)
         then
           begin
             if signame <> "Time"
             then
               print_endline ("WARNING : signature " 
                              ^ signame 
                              ^ " used in a command but not present in the model.");
             y
           end
         else
           (* if the signature signame is variable and primary (the only bigger 
              signature is the hull of signame) then the scope applies to the 
              hull of signame 
           *)
           let greater_sigs, _ = 
             begin
               try 
                 NameMap.find signame (fst sigord)
               with 
                 | Not_found -> failwith ("Elecfile_to_k1.bnds_from_scopes_but:\ 
               signature "
                                          ^ signame ^ " not found.")
             end
           in
           let hull_name =  Ast_ident.to_string @@
             Ast.Hull.to_hull @@ Ast_ident.make signame
           in
           if NameSet.equal greater_sigs 
                (NameSet.add hull_name (NameSet.singleton Names.univ))
           || NameSet.equal greater_sigs (NameSet.singleton hull_name)
           then
             NameMap.add hull_name (x1,x2) y

           else
             (* if the signature is not primary then we print a warning, 
                because the bound is not taken into account 
             *)
           if not (is_primary2 sigord signame )
           then
             begin
               print_endline ("WARNING: A scope was given to signature " 
                              ^ signame
                              ^ " which is not primary. It will be ignored.");
               y
             end
           else
             let min_bnd = min_bound sigord sigmult abstr_sigs signame in
             let max_bnd = max_bound sigord sigmult abstr_sigs signame in
             if min_bnd > max_bnd && (max_bnd <> -1)
             then
               failwith ("Elecfile_to_k1.bnds_from_scopes_but: derived bounds\ 
                          for " ^ signame ^ " are not coherent.")
             else
               (* if the multiplicity of a sig is completely determined by the 
                  model, then we force the bound to this value *)
             if min_bnd = max_bnd
             then
               NameMap.add signame (true, min_bnd) y 
             else
               (* if the required bound is greater than the maximum bound
                  then we force the bound to the maximum bound
               *)
             if x2 > max_bnd && (max_bnd <> -1)
             then
               NameMap.add signame (x1, max_bnd) y
             else
               (* if the required bound is lower than the minimum bound
                  then we force the bound to the minimum bound
               *)
             if x2 < min_bnd
             then
               NameMap.add signame (true, min_bnd) y
             else
               (* else we consider the scope given in the command *)
               NameMap.add signame (x1, x2) y
      )
      typescope_list 
      NameMap.empty
  in
  let prim_sigs = 
    BatSet.filter (is_primary2 sigord) (BatSet.of_enum (NameMap.keys (fst sigord))) 
  in
  let rest = BatSet.diff prim_sigs (BatSet.of_enum (NameMap.keys bounds_from_ts_list)) in
  BatSet.fold 
    (fun x y -> 
       let min_bnd = min_bound sigord sigmult abstr_sigs x in
       let max_bnd = max_bound sigord sigmult abstr_sigs x in
       if min_bnd > max_bnd && (max_bnd <> -1)
       then
         failwith ("Elecfile_to_k1.bnds_from_scopes: derived bounds for "
                   ^ x ^ " are not coherent.")
       else
         (* if the multiplicity of a sig is completely determined by the 
            model, then we force the bound to this value *)
       if min_bnd = max_bnd
       then
         NameMap.add x (true, min_bnd) y
       else
         (* if 3 is greater than the maximum bound
            then we force the bound to the maximum bound
         *)
       if 3 > max_bnd && (max_bnd <> -1)
       then
         NameMap.add x (false, max_bnd) y
       else
         (* if 3 is lower than the minimum bound
            then we force the bound to the minimum bound
         *)
       if 3 < min_bnd
       then
         NameMap.add x (true, min_bnd) y
       else
         (* else we add the scope by default *)       
         NameMap.add x (false, k) y
    )
    rest
    bounds_from_ts_list

(* returns a pair (formula, bounds) from an environment (of type envir_sig), 
   a signame_order, the multiplicity of sigs (of type Profile.signame_mult),
   the list of abstract_sigs and a command *)  
let cmd_to_prop env sigord sigmult abstr_sigs cmd=
  let envalias = envir_to_aliases env in
  match cmd with
    | NamedCmd (qname, Check, bnd, label) -> 
        let cur_assert =
          begin 
            try
              List.find 
                (fun x ->
                   match x.name with
                     |Some xname -> (Ast_ident.to_string xname) 
                                    = (Ast_qname.to_string qname)
                     | None -> false
                )
                env.assertlist
            with
              | Not_found -> 
                  failwith ("elecfile_to_k1: cmd_to_prop: unable to find assertion " 
                            ^ (Ast_qname.to_string qname))
          end
        in
        let formula = conjunct cur_assert.body envalias in
        let bound = 
          begin
            match bnd with
              | None -> 
                  (* let siglist = BatList.of_enum (NameMap.keys (fst sigord)) in *)
                  bnds_from_scopes sigord sigmult abstr_sigs []
              (* default_bounds sigmult (List.filter (is_primary2 sigord) siglist) *)
              | Some ForBut (n, typescope_list) -> 
                  bnds_from_scopes_but sigord sigmult abstr_sigs n typescope_list
              | Some ForTypes typescope_list -> 
                  bnds_from_scopes sigord sigmult abstr_sigs typescope_list
          end
        in
        (formula, bound)

    | NamedCmd (qname, Run, bnd, label) ->
        let predicate =
          begin
            try
              QNameMap.find qname env.predicates
            with
              | Not_found -> 
                  failwith ("elecfile_to_k1: cmd-to-prop: unable to find predicate "
                            ^ (Ast_qname.to_string qname))
          end
        in


        let loca = 
          match predicate.body with
            | [] -> Location.dummy_loc
            | h::q  -> h.loc 
        in

        (* proflist is the list of profiles of the predicate parameters.
           Used in a run command, each profile must be a singleton of a list 
           of length 1.*)
        let bt_list = QNameMap.find qname env.predmap in

        (* this function simplifies a bound type that only consists of a signature. 
           It returns the signature (ast_qname) and a boolean specifying whether 
           the signature is var *) 
        let simplify bt =
          match bt with
            | TRel set -> if BoundType.cardinal set = 1
                then
                  let basetypelist, isvar = BoundType.choose set in
                  match basetypelist with
                    | [base_t] -> 
                        begin
                          match base_t with
                            | Base_Sig signame -> signame, isvar
                            | _ -> failwith "elecfile_to_k1: cmd_to_prop: \ 
                                             problem in a bound type simplification (1)"
                        end
                    | _ -> failwith "elecfile_to_k1: cmd_to_prop: \ 
                                        we do not handle higher-order predicates in commands"
                else
                  failwith "elecfile_to_k1: cmd_to_prop:\ 
                                 ambiguous type for a relation"
            | _ -> failwith  "elecfile_to_k1: cmd_to_prop: simple bound type should be of type TRel"
        in
        let real_bt_list = List.map simplify bt_list in
        (* let prof_list = *)
        (*   begin *)
        (*   try *)
        (*    List.map basic_bt_to_prof bt_list *)
        (*   with *)
        (*   | Not_found -> failwith ("elecfile_to_k1: cmd-to-prop: unable to find profile of predicate " *)
        (*         ^ Ast_qname.to_string qname) *)
        (*   end *)
        (* in *)


        (*let fresh_var_list =
          List.map (fun siglist -> fresh "pred_" ^ (Ast_qname.to_string qname)) 
          real_bt_list
          in*)

        (* we reuse the same variables as declared in the predicate *)
        let var_list =
          List.fold_left
            (fun acclist (dec:Ast_expr.decl) -> acclist@(List.map Ast_ident.to_string dec.names) )
            [] predicate.params
        in

        (* to use in a fold2 call *)
        (* var_name is a string *)
        (* ts_isvar is of type qname*bool *)
        (*  blck is a block *)
        let decl_formula_some blck var_name ts_isvar  =
          let ts, is_var = ts_isvar in
          let range = 
            { expr = EQualName ts;
              loc = loca;
              typ = Some (TRel (BoundType.singleton ([Base_Sig ts], is_var)));
            }
          in
          let decl = 
            make_decl is_var false [Ast_ident.make(var_name)] range false 
          in
          [{ expr = EQuant (`Some, [decl], blck);
             loc = loca;
             typ = Some TBool;
           }]

        in

        let starting_block = predicate.body in 
        let formula_elec_expr = 
          List.fold_left2 decl_formula_some starting_block var_list real_bt_list 
        in
        let formula = conjunct formula_elec_expr envalias in

        let bound = 
          begin
            match bnd with
              | None -> 
                  (* let siglist = BatList.of_enum (NameMap.keys (fst sigord)) in *)
                  (* default_bounds sigmult (List.filter (is_primary2 sigord) siglist) *)
                  bnds_from_scopes sigord sigmult abstr_sigs []
              | Some ForBut (n, typescope_list) -> 
                  bnds_from_scopes_but sigord sigmult abstr_sigs n typescope_list
              | Some ForTypes typescope_list -> 
                  bnds_from_scopes sigord sigmult abstr_sigs typescope_list
          end
        in

        (formula, bound)


    | BlockCmd (bl, _, bnd, label) -> 
        let formula = conjunct bl envalias in
        let bound = 
          begin
            match bnd with
              | None -> 
                  (* let siglist = BatList.of_enum (NameMap.keys (fst sigord)) in *)
                  bnds_from_scopes sigord sigmult abstr_sigs []
              (* default_bounds sigmult (List.filter (is_primary2 sigord) siglist) *)
              | Some ForBut (n, typescope_list) -> 
                  bnds_from_scopes_but sigord sigmult abstr_sigs n typescope_list
              | Some ForTypes typescope_list -> 
                  bnds_from_scopes sigord sigmult abstr_sigs typescope_list
          end
        in
        (formula, bound)

let cmd_is_check cmd =
  match cmd with
    | NamedCmd (_, Check, _, _) -> true
    | BlockCmd (_, Check, _, _) -> true
    | _ -> false

let list_of_check_formulas_and_bounds env sigord sigmult abstr_sigs =
  List.map (cmd_to_prop env sigord sigmult abstr_sigs) 
    (List.filter cmd_is_check env.cmdlist)

let list_of_run_formulas_and_bounds env sigord sigmult abstr_sigs =
  List.map (cmd_to_prop env sigord sigmult abstr_sigs) 
    (List.filter (fun x ->  not (cmd_is_check x)) env.cmdlist)


let string_asserts env=
  let envalias=envir_to_aliases env in
  (* let factprops=facts_to_k1props env.factlist envalias in *)
  (* let facts= List.fold_left  *)
  (*   (fun acc fprop->acc^"\n"^(K1_pretty.string_of_prop fprop)) "" factprops in *)
  let aslist=asserts_to_props env.assertlist envalias in
  let asserts=List.fold_left 
                (fun acc (nameopt, aprop)->
                   let sprop=match nameopt with
                     |None->K1_pretty.string_of_prop aprop
                     |Some id->(Ast_ident.to_string id)^": "^(K1_pretty.string_of_prop aprop)
                   in
                   acc^"\n"^sprop) "" aslist in
  (* "\n*** [K1] Facts ***"^ facts ^ *)"\n\n*** [K1] Assertions ***\n" ^ asserts


