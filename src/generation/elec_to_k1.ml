(*******************************************************************************
 * Time-stamp: <2015-10-29 CET 09:40:01 David Chemouil>
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
open Ast.Expr
open Types
open Typing
open Profile
open Fresh

(* fresh variable related to a term *)
let fresh_of_term term=
  try let range= Union.choose term.profile in
    fresh @@ List.hd range
  with Not_found -> failwith (
        "fresh_of_term: term"^(K1_pretty.string_of_term term)
        ^" has empty profile.")

(* the environment we use. 
   In particular curterm is used for multiplicities, 
   it is the current term we are defining *)

type env_alias = {
  assoc:envir;
  sigord: sig_order;
  predbt: envirlist;
  preds: Ast_par.pred map; (* from Ast_qname to preds *)
  funs: (Ast_qname.t * Ast_par.func) list;
  sigs: (Ast_qname.t list * Ast_par.signature) list; 
  curterm: term option; (* for multiplicities *)
  rootmult: bool; (* for multiplicities, default is 'one' at the root and 'set' below*)
  curthis: term option; (* the current meaning of 'this' *)
  sigtot: signame_order;
  local_names: Ast_qname.t list; (* names to be dereferenced with curthis *)
  arglist : term list; (* the arguments to be applied to a function when we reach it *)
}

let envir_to_aliases env=
  {assoc = env.env_map;
   sigord = env.sign_ord; 
   predbt = env.predmap;
   preds = env.predicates; 
   funs = env.funclist;
   sigs = env.sig_list;
   curterm = None;
   curthis = None;
   rootmult = false;
   sigtot=sigord_toname env.sign_ord;
   local_names = [];
   arglist = [];
  }




(*
   (* put a term in the hole of a term_context *)
   let compose context term=match context with
   | CHole -> term
   | CUnop (op, c) -> TUnop (op, compose c term)
   | CBinopr (op, t,c) -> TBinop (op, t, compose c term)
   | CBinopl (op, c,t) -> TBinop (op, compose c term, t)
*)


(* context for multiplicities 
   Example: x: A some-> one B when evaluating A gives the context x
   None if we are not evaluating multiplicities
*)
(*type mult_context=expr*)


(* from multiplicity to qualifier, Set forbidden *)
let toqual= function
  |`Set -> assert false
  |`Some -> `Some 
  |`Lone -> `Lone
  |`One -> `One 

(* From list of formulas to conjunction *)
let rec conjlist l=match l with
  |[] -> True
  |[f] -> f
  |f::q -> let r=conjlist q in 
      and1 (f,r)


(* replace var x by term y in k1term *)
let rec repl_term k1term x y=match k1term.term with
  | TConstRel _ -> k1term
  | TVarRel _ -> k1term
  | TSort _ -> k1term
  | TVar v-> if x=v then y else k1term
  | TUnop (op, t) -> {k1term with term=TUnop (op, repl_term t x y)}
  | TBinop (op, t1,t2) -> {k1term with term=TBinop (op, repl_term t1 x y, repl_term t2 x y)}
  | TIfThenElse (p, t1,t2) -> {k1term with term=TIfThenElse (repl_prop p x y, repl_term t1 x y, repl_term t2 x y)}
  | TCompr (decls, p) -> 
      let newdecls=List.map 
                     (fun (v,t)->if v=x 
                       then failwith "Elec_to_k1.repl_term: name conflict" 
                       else (v, repl_term t x y))
                     decls
      in {k1term with term=TCompr (newdecls, repl_prop p x y)}

and repl_iexpr k1int x y= match k1int with
  | IConst i -> IConst i
  | IVar n -> IVar n
  | IOp (op, it1, it2) -> IOp (op, repl_iexpr it1 x y , repl_iexpr it2 x y)
  | IMult (i,it) ->IMult (i, repl_iexpr it x y)
  | ICard t -> ICard (repl_term t x y)

(* same in a K1 prop *)
and repl_prop phi x y=match phi with
  | Equal (t1,t2) -> Equal (repl_term t1 x y, repl_term t2 x y)
  | In (t1,t2) -> In (repl_term t1 x y, repl_term t2 x y)
  | Comp (op, it1, it2) -> Comp (op, repl_iexpr it1 x y, repl_iexpr it2 x y)
  (* propositional connectives *)
  | True -> True 
  | False -> False
  | Not p -> not1 (repl_prop p x y)
  | And (p1,p2) -> and1 (repl_prop p1 x y, repl_prop p2 x y)
  | Or (p1,p2) -> or1 (repl_prop p1 x y, repl_prop p2 x y)
  | Impl (p1,p2) -> impl1 (repl_prop p1 x y, repl_prop p2 x y)
  | Iff (p1,p2) -> iff1 (repl_prop p1 x y, repl_prop p2 x y)
  (* future temporal connectives *)
  | Next p -> Next (repl_prop p x y)
  | Always p -> always1 (repl_prop p x y)
  | Eventually p -> Eventually (repl_prop p x y)
  | Until (p1, p2) -> Until (repl_prop p1 x y, repl_prop p2 x y)
  | Release (p1, p2) -> Release (repl_prop p1 x y, repl_prop p2 x y)
  (* past temporal connectives *)
  | Previous p -> Previous (repl_prop p x y)
  | Hist p -> Hist (repl_prop p x y)
  | Once p -> Once (repl_prop p x y)
  | Since (p1, p2) -> Since (repl_prop p1 x y, repl_prop p2 x y)
  (* quantifiers *)
  | Forall (args, t, p) -> forall1 (args, repl_term t x y, repl_prop p x y) 
  | Exists (args, t, p) -> exists1 (args, repl_term t x y, repl_prop p x y) 


let rec repl_tlist phi xlist ylist=
  let (xn,yn)=(List.length xlist, List.length ylist) in
  verify_arg (xn=yn) 
    ("Elec_to_k1 repl_tlist:Replacement lengths do not match: "
     ^(string_of_int xn)^" != "^(string_of_int yn));
  match xlist,ylist with
    |[],[] -> phi
    |v::q1, t::q2 -> let phi'=repl_term phi v t 
        in repl_tlist phi' q1 q2
    | _ -> assert false


let rec repl_plist phi xlist ylist=
  verify_arg (List.length xlist=List.length ylist) "Elec_to_k1 repl_plist:Replacement lengths do not match";
  match xlist,ylist with
    |[],[] -> phi
    |v::q1, t::q2 -> let phi'=repl_prop phi v t 
        in repl_plist phi' q1 q2
    | _ -> assert false

(* replace a list of variables in a block *)
let rec repl_blist bloc xlist ylist= 
  List.map (fun phi->repl_plist phi xlist ylist) bloc

(* 
   We produce a k1 term from a relational expression 
   We assume everything is well-typed, and do not perform any more checks, as it was done in the typing step 
   There is a mult_context in argument 

   We return the K1 term as well as a list of formulas expressing additionnal constraints,
   so the result has type term * (prop list)
*)



let qualtoform qual term flist = 
  let x = fresh_of_term term in
  let y = fresh_of_term term  in
  let form1=exists1([x], term , True) in
  let tx={term with term=TVar x} in
  let ty={term with term=TVar y}  in
  let form2=forall1([x], term , 
                    (forall1 ([y],term, Equal(tx, ty)))) 
  in
  (match qual with 
    | `Some ->  conjlist (form1::flist)
    | `Lone->  conjlist (form2::flist)
    | `One ->  conjlist (form1::form2::flist)
    | `No -> let form=forall1([x],term, False) in
        conjlist (form::flist)
  )

(* from expression to its profile *)
let e_to_prof expression = match expression.typ with
  | None ->
      failwith ("Elec_to_k1.e_to_prof: Profile: untyped expression at "
                ^ Location.to_string expression.loc)
  | Some (TRel r) -> bt_to_prof r
  | Some TBool ->
      failwith
        (Printf.sprintf
           "Elec_to_k1.e_to_prof: Type of %s must be a relation or a set \
            (here: proposition)"
           (Util.PPrintX.to_string @@ Pretty.expr_to_document expression))
  | Some (TVarndef qn) ->
      failwith
        (Printf.sprintf
           "Elec_to_k1.e_to_prof: Type of %s must be a relation or a set \
            (here: undefined %s)"
           (Util.PPrintX.to_string @@ Pretty.expr_to_document expression)
           (Ast_qname.to_string qn)
        )

(* join a list of arguments to an accterm *)
let rec join_appl accterm l env= 
  let signames = sigord_toname env.sigord in
  match l with 
    |[] -> accterm
    |eterm::q -> let newterm={ 
          term=TBinop(Join,eterm, accterm); 
          profile= prof_join signames eterm.profile accterm.profile} 
        in join_appl newterm q env



(* if a name is a relation/function, we turn it into a term, applying arglist *)
let rec qn_to_term qname envalias btexpr elecprof=
  (*debug 
    print_endline ("Looking for "^(Ast.Qname.to_string qname));*)
  let name=qn_to_name qname in
  if sig_exists qname envalias.sigord then 
    (* do we need to know if a signature is variable ? *)
    (*let (_,bvar)=QNameMap.find name envalias.sigord *)
    let sigt={term=TSort name; profile=elecprof} in
    join_appl sigt envalias.arglist envalias
  else (* not signature *)

    try (* function ? *)
      let fct=List.assoc qname envalias.funs in
      (*Cfg.print_debug ("elec_to_k1term: Applying "^(string_of_int @@ List.length envalias.arglist)
        ^ " arguments to function "^ name^"\n");*)
      function_to_term fct envalias.arglist envalias 

    with Not_found  -> (* not function *)
    try let bt=QNameMap.find qname envalias.assoc (* relation ? *)
      in 
      let raw_rel=
        if isvar bt then 
          TVarRel name
        else
          TConstRel name
      in
      (* possible dereferencing *)
      let relterm_deref=
        if List.mem qname envalias.local_names then
          (match envalias.curthis with
            |None-> failwith ("A local name has been given without signature for "^name)
            |Some sigterm -> Cfg.print_debug 
                               ("Derefencing "^name^" with "^ 
                                (K1_pretty.string_of_term sigterm )^"\n");
                (* we get the profile from the environment, to get the global one and not local *)
                let prof=
                  (match bt with 
                    |TRel r->bt_to_prof r
                    |_ -> assert false)
                in
                let relterm={term=raw_rel; profile=prof} in
                {term=TBinop(Join, sigterm, relterm); profile=elecprof}
          )
        else {term=raw_rel; profile=elecprof}
      in
      (* apply all arguments 
         Cfg.print_debug (
         "elec_to_k1term:Applying "^(string_of_int @@ List.length envalias.arglist)
         ^ " arguments to relation "^ name^"\n");*)
      join_appl relterm_deref envalias.arglist envalias

    with Not_found -> (* if nothing is found it is a variable *)
      (* Cfg.print_debug ("The name "^name^" was not found, inferred as a variable\n"); *)
      {term=TVar name; profile= elecprof}

(* boolean saying if we want to propagate arguments or not *)
and prop_args (e:expr)=match e.expr with
  |EBinary(_,BDot, _) -> true
  |EApp(_,_) -> true
  |EQualName _ -> true
  |EAtName _ -> true
  | _ -> false



(* takes a declaration and returns 
   -a list of var terms, 
   -a list of ranges, -
   -a list of constraints;
   -a formula for disjunction, in case d.is_disjoint_variables is true *)
and decl_to_terms d envalias=
  let newnames=List.map id_to_name d.names in
  let (dterm,_)= expr_to_k1term d.range envalias in
  let varterms=List.map (fun n-> {dterm with term=TVar n}) newnames in
  (*formula stating that the variables are disjoint *)
  let disjform = 
    let rec treat x l=
      match l with 
        |[] -> True
        |y::[] ->  not1 (Equal (x,y))
        |y::q -> let frec = and1(treat x q, treat y q) in
            and1(not1 (Equal (x,y)),frec)
    in match varterms with
      |[] -> failwith "Elec_to_k1.decl_to_terms: empty declaration"
      |x::q -> if d.is_disjoint_variables 
          then treat x q
          else True
  in
  (* constraint for the multiplicities, each var must be given in context*)
  let constlist=List.fold_left
                  (fun acc vterm-> 
                     let (_,flist)=
                       expr_to_k1term d.range {envalias with curterm=Some vterm}
                     in flist@acc) 
                  [] varterms
  in (newnames, dterm, constlist, disjform)

and expr_to_k1term elec_expr envalias_init=

  let elecstring=
    (Util.PPrintX.to_string @@ Pretty.expr_to_document elec_expr) 
    ^" at "^(Location.to_string elec_expr.loc)
  in
  let signames = sigord_toname envalias_init.sigord in
  let elecprof=e_to_prof elec_expr in
  (* add a multiplicity 'one' if the context is appropriate, i.e. we are at the root of a definition *)
  let (prime_mult,envalias_init2)=
    if envalias_init.rootmult && envalias_init.curterm <> None then
      (* we verify there is not already a multiplicity 
         and that it is not a cartesian product
         and that the arity is 1 
      *)
      let primres=match elec_expr.expr with
        |EUnary ((UMult _) , _) -> elec_expr.expr
        |ECart (_ ,_ ,_ ,_) -> elec_expr.expr
        | _ -> if arity1 elecprof then
              (Cfg.print_debug ("Mult One Added to "^elecstring ^"\n");
               EUnary ((UMult `One) , elec_expr))
            else elec_expr.expr
      in (primres, {envalias_init with rootmult=false;})
    else (elec_expr.expr, envalias_init)
  in
  (* reset arglist if appropriate *)

  let envalias =
    if prop_args elec_expr 
    then envalias_init2
    else {envalias_init2 with arglist=[]}
  in
  match prime_mult with
    | EThis -> (match envalias.curthis with
          |Some t -> (t,[])
          |None -> failwith "Elec_to_k1.expr_to_k1term: 'this' is undefined in this context"
        )
    (* constants *)
    | EConst c -> (match c with 
          | CNum _ -> failwith "Elec_to_k1.expr_to_k1term: Int not implemented"
          | CNone -> empty_term, []
          | CIden -> id_term , []
          | CUniv -> univ_term, []
          | CInt -> failwith "Elec_to_k1.expr_to_k1term: Int not implemented")
    (* unary operator preceding an expression *)
    | EUnary (op,e) -> 
        (match op with 
          | UMinus -> failwith "Elec_to_k1.expr_to_k1term: Minus: Int not implemented"
          | UMult mult -> (* context must be used !*)
              let (eterm,forms)=expr_to_k1term e envalias in
              let x=fresh_of_term eterm in
              let y=fresh_of_term eterm in
              let xterm={term=TVar x; profile=elecprof} in
              let yterm={term=TVar y; profile=elecprof} in
              let termult=match envalias.curterm with
                | Some xt -> xt
                | None -> failwith "Elec_to_k1.expr_to_k1term: No curterm provided for multiplicity"
              in
              let phi_some = exists1([x], termult, True) in
              let phi_lone=
                forall1([x], termult , 
                        (forall1 ([y],termult, Equal(xterm, yterm)))) 
              in
              let phi_one=
                exists1([x], termult, 
                        (forall1 ([y],termult, Equal(xterm, yterm)))) 
              in
              let multform=match mult with
                |`Some -> [phi_some]
                |`Lone -> [phi_lone]
                |`One -> [phi_one]
                |`Set -> []
              in (eterm, multform@forms)
          | UCard -> failwith "Elec_to_k1.expr_to_K1term: Card _ is not a term but an iexpr"
          (* transpose *)
          | UTilde -> let (x,forms)=expr_to_k1term e envalias in
              {term=TUnop (Tilde, x); profile=elecprof}, forms
          (*trans closure + id:univ->univ*)
          | UStar ->  let (x,forms)=expr_to_k1term e envalias in
              let hat_term={term=TUnop(Trans,x); profile=elecprof} in
              {term=(TBinop(Union,hat_term, id_term)); profile=elecprof}, forms
          (* trans closure *)
          | UHat -> let (x,forms)=expr_to_k1term e envalias in
              {term=(TUnop (Trans, x)); profile=elecprof}, forms
          | UPrime -> let (x,forms)=expr_to_k1term e envalias in
              {term=(TUnop (Prime, x)); profile=elecprof}, forms
          | _ -> failwith "Elec_to_k1.expr_to_k1term: Temporal operators cannot be at the root of terms"
        )
    (* binary operator *)
    | EBinary (e1,op,e2) ->
        let (ke1,forms1)=expr_to_k1term e1 {envalias with arglist=[]}in 
        (* we have to plan for special cases in case of BDot *)
        let (ke2,forms2)=
          (match op with 
            |BDot -> let envargs={envalias with arglist=ke1::envalias.arglist}
                in expr_to_k1term e2 envargs 
            |_ ->expr_to_k1term e2 {envalias with arglist=[]}
          )
        in  
        let forms=forms1@forms2 in
        (match op with 

          (* set & relational operators *)
          | BUnion ->{term=(TBinop(Union, ke1, ke2)); profile=elecprof} , forms
          | BInter -> {term=(TBinop(Inter, ke1, ke2)); profile=elecprof} , forms
          | BMinus -> {term=(TBinop(Diff, ke1, ke2)); profile=elecprof} , forms
          | BOver -> (* e1 over e2= e1 - ( (e2.univ)<: e1) + e2 *)
              let bt2=(match e2.typ with
                    |Some (TRel x)-> TRel x
                    | _ -> failwith "Elec_to_k1.expr_to_k1term: Problem with typing in Override"
                  )
              in
              let newexpr =
                {elec_expr 
                 with expr = 
                        EBinary({e1 
                                 with expr = 
                                        EBinary(e1, 
                                                BMinus, 
                                                {e1 with expr= 
                                                           EBinary({e1 
                                                                    with expr = EBinary(e2, 
                                                                                        BDot, 
                                                                                        {e1 with expr=EConst CUniv; typ= Some bt_univ}); 
                                                                         typ= Some (bt_join_ok envalias.sigord bt2 bt_univ)}, BLProj,e1)}
                                               )},
                                BUnion,
                                e2)}
              in expr_to_k1term newexpr envalias

          | BLProj -> 
              let arities=Union.fold 
                            (fun l acc-> let k=List.length l -1 in
                              if (List.mem k acc) then acc else k::acc)
                            ke2.profile []
              in let rec conjuniv k=(match k with
                    |0-> ke1
                    |_ -> let t=conjuniv (k-1) in
                        let tk=TBinop(Product,t, univ_term) 
                        and pk= prof_prod t.profile univ_term.profile
                        in {term=tk; profile=pk}
                  )
              in let opte1univs=List.fold_left
                                  (fun optacc k -> let tk=conjuniv k in
                                    (match optacc with
                                      |None-> Some tk
                                      |Some acc->Some {term=TBinop(Union, tk, acc);
                                                       profile= Union.union tk.profile acc.profile}
                                    )) None arities 
                                  (* e1univs= e1 * Univ^k, union for all valid k*)
              in (match opte1univs with
                   |None-> failwith "Elec_to_k1.expr_to_k1term: empty profile"
                   |Some e1univs -> {term=(TBinop(Inter, e1univs, ke2 )); profile=elecprof} , forms
                 )  

          | BRProj -> (* symetric of BLProj *)
              let arities=Union.fold 
                            (fun l acc-> let k=List.length l -1 in
                              if (List.mem k acc) then acc else k::acc)
                            ke1.profile []
              in let rec conjuniv k=(match k with
                    |0-> ke2
                    |_ -> let t=conjuniv (k-1) in
                        let tk=TBinop(Product, univ_term, t) 
                        and pk= prof_prod univ_term.profile t.profile 
                        in {term=tk; profile=pk}
                  )
              in let opte2univs=List.fold_left
                                  (fun optacc k -> let tk=conjuniv k in
                                    (match optacc with
                                      |None-> Some tk
                                      |Some acc->Some {term=TBinop(Union, tk, acc);
                                                       profile= Union.union tk.profile acc.profile}
                                    )) None arities 
                                  (* e2univs= Univ^k * e2, union for all valid k*)
              in (match opte2univs with
                   |None-> failwith "Elec_to_k1.expr_to_k1term: empty profile"
                   |Some e2univs -> {term=(TBinop(Inter, e2univs, ke1 )); profile=elecprof} , forms
                 ) 


          | BDot -> 
              if prop_args e2 then 
                (* no need to join, it was done via arglist *)
                ke2 , forms
              else (* below is a non accumulative expression *)
                {term=(TBinop(Join, ke1, ke2 )); profile=elecprof}, forms
          (* logic *)
          | _ -> failwith "Elec_to_k1.expr_to_k1term: Boolean operators do not form terms"
        )
    (* cartesian product with multiplicities à la UML *) 
    | ECart (e1, m1, m2, e2) -> 
        (*let mcont=match envalias.curterm with
          |None -> (* failwith ("Context was not given for multiplicities "^elecstring) *)
          |Some x -> x
          in *)

        (* extract profiles *)
        let prof1=match e1.typ with 
          |Some (TRel x) -> bt_to_prof x
          |None -> failwith ("Elec_to_k1.expr_to_k1term: Untyped e1"^(Location.to_string e1.loc))
          | _ -> failwith "Elec_to_k1.expr_to_k1term: Boolean type in multiplicity"
        in
        let prof2=match e2.typ with 
          |Some (TRel x) -> bt_to_prof x
          |None -> failwith ("Elec_to_k1.expr_to_k1term: Untyped e2"^(Location.to_string e2.loc))
          | _ -> failwith "Elec_to_k1.expr_to_k1term: Boolean type in multiplicity"
        in

        (* update contexts and compute the nested terms and formulas *)

        (* we do a first pass without context to compute ke1 with no constraints *)
        let (ke1_temp,_)=expr_to_k1term e1 envalias in
        (* this allows to give a context for ke2 *)
        let cont2=match envalias.curterm with 
            None -> None
          |Some mcont ->
              let profjoin2 = prof_join signames prof1 mcont.profile in
              Some {term=TBinop(Join, ke1_temp, mcont);
                    profile= profjoin2}  
        in
        let (ke2,forms2)=
          expr_to_k1term e2 {envalias with curterm=cont2;rootmult=false} in  
        (* We finally compute the good context for ke1 with constraints *)
        let cont1=match envalias.curterm with
            None -> None
          |Some mcont ->
              let profjoin1 = prof_join signames mcont.profile prof2 in
              Some {term=TBinop(Join, mcont, ke2);
                    profile= profjoin1}
        in
        let (ke1,forms1)=
          expr_to_k1term e1 {envalias with curterm=cont1;rootmult=false} in
        (* add the formulas corresponding to the current level *)

        let newform1= match m1 with
          | `Set -> forms1
          | _ -> let newvar= fresh_of_term ke2 in
              (match (envalias.curterm,cont1) with
                |(Some mcont, Some cont1)->

                    let newterm={ke2 with term=TVar newvar} in
                    let internal={
                      term=TBinop (Join,mcont,newterm);
                      profile=cont1.profile} in
                    let prop1=qualtoform (toqual m1) internal [] 

                    (* we quantify on context * ke2 *)

                    in  (forall1 ([newvar],ke2, prop1))::forms1
                | _ -> failwith ("Elec_to_k1.expr_to_k1term: only Set multiplicity is allowed here (left) : "^elecstring))
        in  
        let newform2= match m2 with
          | `Set -> forms2
          | _ -> let newvar= fresh_of_term ke1 in
              (match (envalias.curterm,cont2) with
                |(Some mcont, Some cont2)->
                    let newterm={ke1 with term=TVar newvar} in
                    let internal={
                      term= TBinop (Join,newterm,mcont);
                      profile=cont2.profile} in
                    let prop2=qualtoform (toqual m2) internal [] 
                    in  (forall1 ([newvar],ke1, prop2))::forms2
                | _ -> failwith ("Elec_to_k1.expr_to_k1term: only Set multiplicity is allowed here (right) : "^elecstring))
        in  
        {term=(TBinop(Product, ke1, ke2)); profile=elecprof} , newform1@newform2


    (* let (local definition) *)
    | ELet (deflist, bloc) ->(match bloc with
          |[]->assert false
          |[e]-> (match e.typ with
                |None -> failwith ("Elec_to_k1.expr_to_k1term: 'Let' Expression must be typed at "^(Location.to_string e.loc))
                |Some (TRel r) -> let (k1term,flist)=expr_to_k1term e envalias in
                    let (vars, terms, phi)=List.fold_left
                                             (fun (acc1,acc2,accform) def-> 
                                                let vname=id_to_name def.name in
                                                let vterm={term=TVar vname; 
                                                           profile= match def.expr.typ with
                                                             |Some (TRel r) -> bt_to_prof r
                                                             | _ -> failwith "Elec_to_k1.expr_to_k1term: range untyped in Let"}
                                                in
                                                let (t,flist)=expr_to_k1term def.expr {envalias with curterm= Some vterm} in
                                                match accform with 
                                                  |True -> (vname::acc1, t::acc2, conjlist flist)
                                                  |_ -> (vname::acc1, t::acc2, and1(conjlist flist, accform))
                                             ) ([],[],True) deflist
                    in 
                    Cfg.print_debug ("repl_tlist of "^(K1_pretty.string_of_term k1term)^"\n");
                    (repl_tlist k1term vars terms),[phi]
                | _ -> failwith "Elec_to_k1.expr_to_k1term: Not a relation"
              )
          | _::_ ->  failwith "Elec_to_k1.expr_to_k1term: Not a relation"
        )

    | EIte (e1,e2,e3) -> 
        let p1=expr_to_k1prop e1 envalias in
        let (t2,l2)=expr_to_k1term e2 envalias in
        let (t3,l3)=expr_to_k1term e3 envalias in
        let f2 = conjlist l2 in
        let f3 =  conjlist l3 in
        let newform= (* p1=> l2 and (not p1)=> l3 *)
          and1(K1.impl1( p1, f2), impl1(not1 p1, f3))
        in {term=TIfThenElse (p1,t2,t3); profile=elecprof}, [newform]


    (* ident prefixed by '@': ident shouldn't be dereferenced *)
    (* always in environment ? *)
    | EAtName id-> 
        let bt=match elec_expr.typ with
          |Some x -> x
          |None -> failwith "Elec_to_k1.expr_to_k1term: should be typed" in
        (* we remove local names to type it globally *)
        (qn_to_term (Ast_qname.local id) {envalias with local_names=[]} bt elecprof), [] 
    (* qualified name *)
    | EQualName qname -> 
        let bt=match elec_expr.typ with
          |Some x -> x
          |None -> failwith "Elec_to_k1.expr_to_k1term: should be typed" in
        (* Cfg.print_debug ("Translating "^(qn_to_name qname)
           ^" at "^(Location.to_string elec_expr.loc)^"\n"); *)
        qn_to_term qname envalias bt elecprof, [] 
    (* relation defined by comprehension *)
    | ECompr (decl_list , bloc)  ->
        (*convert 1 declaration into a list of (varlist * term) *)
        let rec process_decls=(function
              |[] -> [],[]
              |d::q -> 
                  let (names, trange, constlist, disjform)= decl_to_terms d envalias in
                  let links=List.map (fun n-> (n,trange)) names in
                  let (rest,flist) = process_decls q in
                  (links@rest, constlist@flist))
        in 
        let (vtlist, flist)=process_decls decl_list in
        let phibloc=and1(conjunct bloc envalias, conjlist flist) in
        {term= TCompr (vtlist, phibloc);
         profile=elecprof}, []

    (* function/relation application *)
    | EApp (f, expr_list) -> 
        let rec build_list l=match l with
          |[]-> [], []
          |e::q -> let (lq,form)=build_list q in
              let (et, ef)=expr_to_k1term e envalias in
              et::lq, ef@form
        in
        let (termlist, forms)= build_list expr_list in

        if prop_args f then (* We just pass the arglist to f *) 
          let envargs={envalias with arglist=termlist@envalias.arglist} in
          let (res, resforms)=expr_to_k1term f envargs
          in (res,forms@resforms)
        else (* we join all elemnts to the expression f *)
          let ef,flist=expr_to_k1term f envalias in
          let res=join_appl ef termlist envalias in
          (res, forms@flist)

(*
       (* dealing with a function applied to some arguments *)
       begin
       (* Julien's code *)
       match f.expr with

       | EQualName fname ->
       begin
       let rec find_function env fname =
       match env with
       | (fqname, fct)::q when fqname = fname -> fct
       | t::q -> find_function q fname      
       | [] -> failwith ("Elec_to_k1: expr_to_k1_term: function " ^ 
       Ast_qname.to_string fname ^ " not found")
       in    
       let fct = find_function envalias.funs fname in
       let f_term, f_form = function_to_term fct expr_list envalias in
       let prof = 
       match fct.returns.typ with
       | Some (TRel bt) -> bt_to_prof bt
       | _ -> failwith "elec_to_k1: expr_to_k1term: return type of function is not correct"
       in
       (
       { term = f_term;
       profile = prof;
       }
       ,
       []
       ) 
       end
       |   _ -> failwith ("Elec_to_k1: expr_to_k1_term: incorrect function call : " ^ elecstring)
       end
    *)
    (*end of Julien's code *)

    (* let (fterm,flist) =expr_to_k1term f envalias in (\* this assumes we can evaluate f as a relation, thanks to the environment *\) *)
    (* let rec appl accterm acclist l= *)
    (*  (match l with *)
    (*   |[]->accterm, acclist *)
    (*   |e::q->let (eterm,eflist)=expr_to_k1term e envalias in *)
    (*       let newterm={ *)
    (*      term=TBinop(Join,eterm, accterm); *)
    (*      profile= prof_join signames eterm.profile accterm.profile} *)
    (*       (\* BUG? it is really flist, or more likely, eflist?? *\) *)
    (*       in appl newterm (flist@acclist) q *)
    (* ) *)
    (* in appl fterm flist expr_list  *)

    |EBlock [e] -> expr_to_k1term e envalias
    | _ -> failwith ("Elec_to_k1.expr_to_k1term: Wrong argument of Expression to K1 Term: "^elecstring)

(* when the expression represents an integer *)
and expr_to_k1iexpr elec_expr envalias=
  let elecstring=
    (match elec_expr.typ with 
      |Some TBool -> "Bool: "
      |Some (TRel _) -> "Rel: "
      |Some (TVarndef qname) -> "Undefined "^Ast_qname.to_string qname^" : "
      |None -> "Not_Typed : ")
    ^(Util.PPrintX.to_string @@ Pretty.expr_to_document elec_expr) 
    ^" at "^(Location.to_string elec_expr.loc)
  in
  verify_arg (Types.opt_is_int elec_expr.typ) ("Elec_to_k1.expr_to_k1prop: Expression must be an integer :"^elecstring);
  match elec_expr.expr with
    |EUnary (UCard,e) -> let (t,forms)=expr_to_k1term e envalias in
        if forms <> [] then Cfg.print_debug ("Warning: constraint formulas in int term ignored in "^elecstring);
        ICard t
    |EConst (CNum i) -> IConst i
    | _ -> failwith "expr_to_K1iexpr:Unknown integer construct"

(* produce a conjunction from a block of expressions *)
and conjunct bloc envalias = match bloc with 
  |[] -> True
  |[e] -> expr_to_k1prop e envalias
  |e::q -> and1 (expr_to_k1prop e envalias, conjunct q envalias)

(* from a predicate and a list of arguments (expressions) to a formula *)
and pred_to_form (pred:Ast_par.pred) args envalias_init=
  let envalias={envalias_init with curterm=None} in (*to avoid adding some 'one'*)
  let open Ast_par in
  let open Ast_expr in
  (* we reverse the order of the two lists to win some time *)
  let xlist=List.fold_left 
              (fun acc dec-> 
                 let vars=List.map id_to_name dec.names
                 in vars@acc)
              [] pred.params
  in
  let (argterms, flist)=List.fold_left (
        fun (accarg,accf) arg->
          let (targ, f)=expr_to_k1term arg envalias
          in targ::accarg, f@accf
      ) 
        ([],[]) args in
  let pbody=List.map (fun x -> expr_to_k1prop x envalias) pred.body in
  let res=repl_blist pbody xlist argterms in
  and1 (conjlist res, conjlist flist)

(* from a function and a list of arguments (terms) to a K1 term 
   warning: we ignore the K1 prop generated by f.body, is it ok ?*)
and function_to_term (fct : Ast_par.func) args envalias=
  let open Ast_par in
  let open Ast_expr in
  (* we reverse the order of the two lists to win some time *)
  let xlist =
    List.fold_left 
      (fun acc dec-> 
         let vars=List.map id_to_name dec.names in 
         vars@acc)
      [] fct.params
  in
  (*let (argterms, flist) =
    List.fold_left 
    (fun (accarg,accf) arg->
    let (targ, f)=expr_to_k1term arg envalias in 
    targ::accarg, f@accf
    ) 
    ([],[]) 
    args 
    in*)
  let t_body, f_body  = expr_to_k1term  fct.body envalias in
  (* we keep only the good number of arguments for fct (in reverse order,
     leaving the rest to be joined with the result 
  *)
  let (argterms, rest)=
    let rec keep l l2 accargs=
      match (l,l2) with
        | _, [] -> (accargs, l)
        | [], _ -> failwith "Not enough arguments !"
        | t1::q1, t2::q2 -> keep q1 q2 (t1::accargs)
    in keep args xlist []
  in
  (* we compute the result of the function *)
  let res_fct = repl_tlist t_body xlist argterms 
  (* we join the rest to the result *)
  in join_appl res_fct rest envalias




(* produce a k1 proposition from a boolean expression *)
and expr_to_k1prop elec_expr envalias= 
  let elecstring=
    (match elec_expr.typ with 
      |Some TBool -> "Bool: "
      |Some (TRel _) -> "Rel: "
      |Some (TVarndef qname) -> "Undefined "^Ast_qname.to_string qname^" : "
      |None -> "Not_Typed : ")
    ^(Util.PPrintX.to_string @@ Pretty.expr_to_document elec_expr) 
    ^" at "^(Location.to_string elec_expr.loc)
  in
  verify_arg (elec_expr.typ= Some TBool) ("Elec_to_k1.expr_to_k1prop: Expression must be a formula :"^elecstring);
  match elec_expr.expr with

    (* block = possibly-empty list of expressions  *)
    | EBlock bloc -> conjunct bloc envalias

    (* quantified formulas *)
    | EUnary (op,e) -> (match op with 
          | UMinus -> failwith "Elec_to_k1.expr_to_k1prop: unary minus not treated "
          | UNot -> not1 (expr_to_k1prop e envalias)
          | UQual qual -> let (res, flist)=expr_to_k1term e envalias in
              qualtoform qual res flist
          | UAlways -> Always (expr_to_k1prop e envalias)
          | UEventually -> Eventually (expr_to_k1prop e envalias)
          | UNext ->Next (expr_to_k1prop e envalias)
          | UHist -> Hist (expr_to_k1prop e envalias)
          | UOnce -> Once (expr_to_k1prop e envalias)
          | UPrevious -> Previous (expr_to_k1prop e envalias)
          | _ -> failwith "Elec_to_k1.expr_to_k1prop: Not a proposition !"
        )

    |EBinary (e1, op, e2) ->
        let ke1=expr_to_k1prop e1 envalias in 
        let ke2=expr_to_k1prop e2 envalias in 
        (match op with 
          (* logic *)
          | BOr -> or1 ( ke1, ke2 )
          | BAnd -> and1 (ke1,ke2)
          | BImp ->  impl1 (ke1,ke2)
          | BIff ->  iff1 (ke1, ke2)
          | BUntil -> Until(ke1,ke2)
          | BSince -> Since (ke1,ke2)
          | BUnion
          | BInter
          | BMinus
          | BOver
          | BLProj
          | BRProj
          | BDot -> assert false
        )
    | EQuant (quant, decl_list, bloc) ->
        (* build is an auxiliary function composing elements into a
           formula if is_disj is false then disjform will always be
           True

           Commented additionnal disjform if build is already called

           build returns (phi_yes, phi_no), where psi must be negated by the caller
           the meaning is (phi and not psi)
           this is to deal with constructs such as No x,y| phi

        *)
        let rec build (vars, trange, phi, is_disj, disjform) quantif=
          let phi2= if is_disj then and1(disjform, phi) else phi in
          let phi_some=
            List.fold_right 
              (fun v accphi ->exists1 ([v], trange, accphi))
              vars
              phi2
          in
          let phi_atleast_two=
            let newnames= List.map (fun x-> fresh_of_term trange) vars in
            let newterms=List.map 
                           (fun x->{trange with term=TVar x}) newnames in
            let equalform=
              let rec proc= function 
                |[],[] -> True
                |[x],[y] -> Equal ({trange with term=TVar x},y)
                | x::qx, y::qy -> and1 (proc ([x],[y]), proc (qx,qy))
                | _ -> assert false
              in proc (vars,newterms)
            in let newphi=repl_plist phi2 vars newterms in
            (* exists x,y phi(x) and phi(y) and not x=y *)
            List.fold_right 
              (fun (v, r) res -> exists1 ([v], r, res)) 
              (List.map (fun v -> (v, trange)) (vars@newnames))
              (and1(and1(phi2, newphi), not1 equalform))
          in
          (match quantif with
            | `All -> let phi2=if is_disj then impl1(disjform, phi) else phi in
                let phi_yes=List.fold_right 
                              (fun v accphi ->forall1 ([v], trange, accphi))
                              vars
                              phi2
                in (phi_yes, False)

            | `Some -> (phi_some, False)
            | `Lone->  (True, phi_atleast_two)


            (* One = Lone and Some (cowboy) *)
            | `One -> (phi_some, phi_atleast_two)

            (* No x:phi = Not (Some x:phi) *)
            | `No -> (True, phi_some)

          ) in
        let rec mainform l=(match l with
              |[] -> conjunct bloc envalias
              | d::q ->
                  (* warning ! here Q x, Qy phi means Qx | Qy | phi except for Q=No *)
                  let (newnames, trange, constlist,disjform)= decl_to_terms d envalias
                  in let formq = mainform q in
                  let (phi_yes,phi_no)=build 
                                         (newnames, trange, formq, d.is_disjoint_variables, disjform)
                                         quant
                  in and1(and1(phi_yes, not1 phi_no),conjlist constlist)
            ) in
        mainform decl_list


    (* let (local definition) *)
    | ELet (deflist, bloc) ->
        let defe_to_form e=(match e.typ with
              |None -> failwith ("Elec_to_k1.expr_to_k1prop: 'Let' Proposition must be typed at "^(Location.to_string e.loc))
              |Some TBool -> let p=expr_to_k1prop e envalias in
                  let (vars, terms, phi)=List.fold_left
                                           (fun (acc1,acc2,accform) def-> 
                                              let vname=id_to_name def.name in
                                              let (t,flist)=expr_to_k1term def.expr envalias in
                                              match accform with 
                                                |True -> (vname::acc1, t::acc2, conjlist flist)
                                                |_ -> (vname::acc1, t::acc2, and1(conjlist flist, accform))
                                           ) ([],[],True) deflist
                  in and1(repl_plist p vars terms, phi)
              | _ -> failwith "Elec_to_k1.expr_to_k1prop: Not a formula" 
            )
        in
        (match bloc with
          |[]->assert false
          |[e]-> defe_to_form e

          | _::_ ->  let flist=List.map defe_to_form bloc 
              in conjlist flist
        )
    | EQualName qn -> (* the name of a predicate without argument is allowed *)
        let pred=try
            mapfind qn envalias.preds
          with Not_found -> let nbpreds = string_of_int @@ QNameMap.cardinal envalias.preds in
            failwith ("Elec_to_k1.expr_to_k1prop: Unknown predicate name:"^(Ast_qname.to_string qn)^", Predicates known: "^nbpreds)
        in pred_to_form pred [] envalias
    (* comparison of expressions *)
    | EComp (e1, op, e2) -> 
        if opt_is_int e1.typ then (* integer case *)
          let i1=expr_to_k1iexpr e1 envalias in
          let i2=expr_to_k1iexpr e2 envalias in
          let compK1=(match op with 
                | CLt -> Lt
                | CGt -> Gt
                | CLte -> Lte
                | CGte -> Gte
                | CEq -> Eq
                | CNeq-> Neq
                | _ -> failwith ("Not an integer comparison operator: "^elecstring)
              ) 
          in Comp(compK1, i1, i2)

        else (* comparison of relational terms *)
          let (t1,l1)=expr_to_k1term e1 envalias in

          let (psi,l2)=(match op with
                | CEq -> let (t2,l2)=expr_to_k1term e2 envalias in Equal (t1,t2), l2
                | CNeq -> let (t2,l2)=expr_to_k1term e2 envalias in not1 (Equal (t1,t2)),l2
                | CIn -> let (t2,l2)=expr_to_k1term e2 {envalias with curterm=Some t1}
                (* warning: duplication of information, weird...
                   probably for multiplicity issues*)
                    in and1(In( t1, t2), conjlist l2),l2
                | CNotIn -> let (t2,l2)=expr_to_k1term e2 {envalias with curterm=Some t1}
                (* warning: we assume there is no need to add l2 constraints in this case *)
                    in not1 (In (t1, t2)), l2          

                | _ -> failwith ("Elec_to_k1.expr_to_k1prop: Unknown comparison operator: "^elecstring)
              )
          in 
          let phi= and1(conjlist l1 , conjlist l2) in
          and1(phi,psi)
    (* ... implies ... else ... (no else == "else true") *)
    | EIte (e1,e2,e3) -> 
        let p1= expr_to_k1prop e1 envalias in
        let p2= expr_to_k1prop e2 envalias in
        let p3= expr_to_k1prop e3 envalias in
        (* p1=> p2 and (not p1)=> p3 *)
        and1(impl1( p1, p2), impl1(not1 p1, p3))
    (* predicate application *)
    | EApp (predexpr, expr_list) ->
        (match predexpr.expr with
          |EQualName predname ->
              (* hardcoded total order *)
              if Ast.Qname.to_string predname="pred/totalOrder" then
                match expr_list with
                  |[elem;first;succ] ->
                      let tot_expr=Typing.totpred elem first succ elec_expr in
                      expr_to_k1prop tot_expr envalias
                  | _ -> failwith "Elec_to_k1.expr_to_k1prop: Wrong arguments of pred/totalOrder\n"
              else
                let pred=try mapfind predname envalias.preds 
                  with Not_found -> 
                    Printf.printf "Error in predicates, list of known:\n";
                    QNameMap.iter (fun qn _ -> Printf.printf "%s \n" (qn_to_name qn)) envalias.preds;
                    failwith ("Elec_to_k1.EApp Unknown predicate:"^(Ast_qname.to_string predname)^" in "^elecstring)
                in pred_to_form pred expr_list envalias
          | _ -> failwith "Elec_to_k1.expr_to_k1prop: Application Proposition must start with Predicate name")
    |_ -> failwith ("Elec_to_k1.expr_to_k1prop: Wrong argument of Expression to K1 Prop: "^elecstring)




