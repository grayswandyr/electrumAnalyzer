(*****************************************************************************
 * Time-stamp: <2015-10-29 CET 10:11:35 David Chemouil>
 *
 * Electrum Analyzer 
 * Copyright (C) 2014-2015 Onera; (C) 2015 IRIT
 * Authors: 
 *   Denis Kuperberg <denis DOT kuperberg AT gmail DOT com>
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
typing.ml -- computes the bound type of Electrum expressions
 ****************************************************************************)
open Batteries
open Ast_expr
open Types
open Faulty
open Faulty.Infix
open Faulty.Monad
open Ast_expr
open Ast_ctrl
open Ast_par
open Ast_file
open Names

(* module encoding maps for which the type of the keys is name *)
module NameMap = Map.Make(struct type t = name let compare = compare end)


(* full environment *)

type envir_sig = 
	{
	env_map : envir;
	sign_ord:sig_order;
	cursig:bound_type option;
	predmap: envirlist; (* list of arguments of each predicate *)
	predicates: pred map;
	facts_typed: bool;
	sig_list: (Ast_qname.t list * signature) list; (* names are updated from ident to qnames*)
	funclist: (Ast_qname.t * func) list;
	factlist: fact list;
	cmdlist: cmd list;
	assertlist: assertion list;
	last_try:bool;
	}


let envirsig_to_string envsig=
  Printf.sprintf 
	"\n*** [Electrum] Signatures  ***\n%s \n\
	*** [Electrum] Types  ***\n%s\n\
	*** [Electrum] Predicates  ***\n%s\n"
	 (* Affichage debug nom des predicats\n%s\n *)
	(sigmap_to_string envsig.sign_ord)
	(envir_to_string envsig.env_map)
	(envirlist_to_string envsig.predmap)
 (* (Util.ListX.to_string String.print @@ List.map (Ast_qname.to_string) (List.of_enum (QNameMap.keys envsig.predicates))) *)
	


let empty_envir = {
	env_map=emptymap;
	sign_ord= emptymap;
	cursig=None;
	predmap=QNameMap.empty;
	predicates=emptymap;
	facts_typed= false;
	sig_list = [];
	funclist = [];
	factlist = [];
	cmdlist = [];
	assertlist= [];
	last_try=true;
	}



let update_sigs (qns,s) siglist=
	if List.exists (fun (a,_)-> a=qns) siglist
	 then siglist else (qns,s)::siglist




(* remove unknown types *)
let purge env=
	{env with env_map=(QNameMap.filter (fun x bt-> not (bt_isvarndef bt)) env.env_map);
			predmap=QNameMap.filter (fun x l->List.for_all (fun bt->not (bt_isvarndef bt)) l) env.predmap;
			facts_typed=true;
			}

(* number of undefined stuff *)
let nb_remain env= 
	let rmenv=QNameMap.cardinal (QNameMap.filter (fun x bt-> bt_isvarndef bt) env.env_map)
	in
	let rmpred= QNameMap.cardinal (QNameMap.filter (fun x btlist -> 
			List.exists (fun bt-> bt_isvarndef bt ) btlist
			) env.predmap)
	in rmenv+rmpred

(* returns a nondef element, can raise Not_found*)
let some_remain env= 
	let bt=try 
		let (_,x)=QNameMap.choose (QNameMap.filter (fun x bt-> bt_isvarndef bt) env.env_map) 
		 in x
		with Not_found -> match
			QNameMap.choose (QNameMap.filter (fun x l->
			match l with 
				|[]-> false
				|t::q -> bt_isvarndef t)
			 env.predmap)
			with 
			| _, t::q -> t
			| qn, [] -> assert false
	in bt_remain bt
	


(* Functions for replacing a signature by another in a file *)
(* replace a qname by its new value if x->value*)
let repl x value a = if a=x then value else a 

let replace_list x value= List.map (repl x value)

(* in an import list *)
let rec rep_imp x value (name, params, al)= (name, replace_list x value params, al)

(* in a bound type *)
let rep_bt x value bt = match bt with
	|TBool -> TBool
	|TVarndef qn -> TVarndef (repl x value qn)
	|TRel r -> let rep_base b=match b with
		| Base_INT -> Base_INT
		| Base_UNIV -> Base_UNIV
		| Base_Sig s -> Base_Sig (repl x value s)
		| Base_Ndef n-> Base_Ndef (repl x value n)
		in
		TRel (BoundType.fold (fun (l,b) acc ->
			BoundType.add (List.map rep_base l, b) acc) r BoundType.empty)

(* in an expression, but here value is a prim_expr *)
let rec rep_expr x valprim (expression:expr)=
 let rep=rep_expr x valprim in 
 let newprim = match expression.expr with
  | EThis -> EThis
  | EConst x -> EConst x
  | ELet (deflist, bloc) -> ELet (List.map (rep_def x valprim) deflist, rep_block x valprim bloc)
  | EQuant (quant, decl_list, bloc ) -> EQuant (quant, List.map (rep_decl x valprim) decl_list, rep_block x valprim bloc)
  | EUnary (op, exp) -> EUnary (op, rep exp)
  | EBinary (e1,op,e2) -> EBinary (rep e1, op, rep e2)
  | ECart (e1,m1,m2,e2) -> ECart (rep e1, m1, m2 , rep e2)
  | EComp (e1,op,e2) -> EComp (rep e1, op, rep e2)
  | EIte (e1,e2,e3) -> EIte (rep e1, rep e2, rep e3)
  | EApp (e, el) -> EApp (rep e, rep_block x valprim el)
  | EAtName id -> EAtName id   (*this is called before typing, so no need to replace in the type *)
  | EQualName a ->  if x=a then valprim else EQualName a
  | EBlock bloc -> EBlock (rep_block x valprim bloc)
  | ECompr (decl_list, bloc) -> ECompr (List.map (rep_decl x valprim) decl_list, rep_block x valprim bloc)
  (* in let newtyp = match expression.typ with
  |None -> None
  |Some bt -> Some (rep_bt x value bt) *)
  (* we keep the previous typ , it should not change *)
  in {expression with expr= newprim;}

(* in a block *)
and rep_block x valprim bloc= List.map (rep_expr x valprim) bloc

(* in a declaration *)
and rep_decl x valprim dec= {dec with range=rep_expr x valprim dec.range}

(* in a definition *)
and rep_def x valprim def={def with expr=rep_expr x valprim def.expr}

(* in a signature declaration *)
and rep_sig x value s=let open Ast_par in
	let valprim=EQualName value in
	let newext= match s.extends with
		|Some (Extends name) -> Some (Extends (repl x value name))
		|Some (In namelist) -> Some (In (List.map (repl x value) namelist))
		|None -> None
	in let newfields=List.map (rep_decl x valprim) s.fields
	in let newfact= match s. fact with
		|Some b -> Some (rep_block x valprim b)
		|None -> None
	in {s with extends=newext; fields=newfields; fact=newfact}

(* in a fact *)
and rep_fact x value (f:Ast_par.fact)=
	let valprim=  EQualName value in
	{f with body=rep_block x valprim f.body}

(*in a predicate *)                                       
and rep_pred x value (p:Ast_par.pred)= 
	let valprim=  EQualName value in
	let newpar= List.map (rep_decl x valprim) p.params in
	{p with params=newpar; body= rep_block x valprim p.body}

(* in a function *)  
and rep_func x value (f:Ast_par.func) = 
	let valprim=EQualName value in
	let newpar= List.map (rep_decl x valprim) f.params in
	let newret= rep_expr x valprim f.returns in
	let newbody= rep_expr x valprim f.body in
	{f with params=newpar; returns=newret; body=newbody}

and rep_assert x value (a:Ast_par.assertion)= {a with body=rep_block x (EQualName value) a.body}

(* in a paragraph *)
and rep_par x value par= let open Ast_par in
 match par with
  | Sig s -> Sig (rep_sig x value s)
  | Enum e -> Enum e
  | Fact f-> Fact (rep_fact x value f)
  | Pred p -> Pred (rep_pred x value p)
  | Fun f -> Fun (rep_func x value f)
  | Assert a -> Assert (rep_assert x value a)

(* in a command *)
and rep_cmd x value cmd= let open Ast_ctrl in
 match cmd with 
  | NamedCmd (qname, cmd_type, optscope, id_opt) -> cmd
  | BlockCmd (bloc, cmd_type, optscope, id_opt) ->
	let repl_scopes scopelist=
		List.map (fun (b,i,qn)->(b,i,repl x value qn)) scopelist
	in
	let valprim = EQualName value in
	let newscope=match optscope with
		|None -> None
		|Some (ForBut (i,scopelist))-> Some (ForBut (i,repl_scopes scopelist))    
		|Some (ForTypes scopelist) -> Some (ForTypes (repl_scopes scopelist))   
	in BlockCmd(rep_block x valprim bloc, cmd_type, newscope, id_opt)

(* in a imp_par list *)
let rec replace_iplist x value l = 
	match l with
	|[] ->[]
	|(Imp i)::q -> (Imp (rep_imp x value i))::(replace_iplist x value q)
	|(Parag p)::q -> (Parag (rep_par x value p))::(replace_iplist x value q)


(* env1 + pref/newenv *)
let env_concat_pref env1 pref newenv params=
	let open Ast_qname in
	let newmap=
		QNameMap.fold (fun name bt acc-> env_add 
				(add_pref pref name) 
				(bt_addpref_except bt pref params)
				 acc) newenv.env_map env1.env_map in
	let newsig=
		sig_union env1.sign_ord (sig_addpref pref newenv.sign_ord) in
	let newpred=
		QNameMap.fold (fun name btl acc-> map_add 
		(add_pref pref name)
		(btlist_addpref_except btl pref params)
		 acc) newenv.predmap env1.predmap in
		 
	
	
	let newboolfacts=
		env1.facts_typed && newenv.facts_typed in
	(* names to modify *)
	let locnames= 
		(* signatures *)
		(List.fold_left (fun acc (qns,_)->qns@acc) [] newenv.sig_list )
		(* predicates *)
		@
		(QNameMap.fold (fun qn _ acc->qn::acc) newenv.predmap [])
	in
	let newnames=
		List.map (add_pref pref) locnames in
	let newpredicates=
		(* first the images *)
		let newimg=
			List.fold_left2 
				(fun accmap name newname->
					QNameMap.map (rep_pred name newname) accmap)
				newenv.predicates locnames newnames
		in
		(* then the names *)
		QNameMap.fold
			(fun qn p acc-> map_add (add_pref pref qn) p acc) newimg env1.predicates
	in
	(* generic function for changing for locnames to newnames using f_repl *)
	let repl_list local_list f_repl =
		List.fold_left2 
			(fun acclist name newname->
				List.map (f_repl name newname) acclist)
			local_list locnames newnames in
			
	(* same with name as first field *)
	let repl_list_name local_list f_repl =
		List.fold_left2 
			(fun acclist name newname->
				List.map 
					(fun (qn,x) -> 
						(repl name newname qn),(f_repl name newname x))
						 acclist
					)
			local_list locnames newnames in
			
	(* same with name list as first field *)
	let repl_list_namelist local_list f_repl =
		List.fold_left2 
			(fun acclist name newname->
				List.map 
					(fun (qns,x) -> 
						(List.map (repl name newname) qns),(f_repl name newname x))
						 acclist
					)
			local_list locnames newnames in
	let rec concat_lists l1 l2=
		match l1 with 
		|[] -> l2
		|t1::q1 -> if List.mem t1 l2 then concat_lists q1 l2 else 
			t1::(concat_lists q1 l2)
	in
	let newsig_list=
		concat_lists 
		env1.sig_list
		(repl_list_namelist newenv.sig_list rep_sig) in
	(*Printf.printf "Newsigs :\n";
	List.iter (fun (qns,_)->List.iter 
		(fun qn -> Printf.printf "%s, " @@ Ast_qname.to_string qn) qns; print_newline()) newsig_list;*)
	let newfunclist=
		concat_lists 
		env1.funclist
		(repl_list_name newenv.funclist rep_func) in
	let newfactlist=
		concat_lists 
		env1.factlist
		(repl_list newenv.factlist rep_fact) in
	let newcmdlist=
		concat_lists 
		env1.cmdlist
		(repl_list newenv.cmdlist rep_cmd) in
	let newassertlist=
		concat_lists 
		env1.assertlist
		(repl_list newenv.assertlist rep_assert) in

	
	{	env_map = newmap;
		sign_ord = newsig;
		cursig = None;
		predmap = newpred;
		predicates = newpredicates;
		facts_typed = newboolfacts;
		sig_list = newsig_list;
		funclist = newfunclist;
		factlist = newfactlist;
		cmdlist = newcmdlist;
		assertlist = newassertlist;
		last_try=env1.last_try;
		}


(* remove a list of signatures from an environment *)
let siglist_remove siglist env=
	let newsig=List.fold_left (fun accsig name->
		QNameMap.remove name accsig) env.sign_ord siglist
	in {env with sign_ord=newsig;}


(* compute the bound type of a function 
it is arg1 * arg2 *..* argn * return_type
*)
let bt_func (f:Ast_par.func)=
  let bt_body=match f.body.typ with
	|Some bt -> bt
	|None -> failwith ("Untyped body of function "^(Ast_ident.to_string f.name))
  in
  List.fold_left
	(fun acc decl -> 
	    let btarg= 
			match decl.range.typ with
			|Some bt -> bt
			|None -> failwith ("Untyped argument of function "^(Ast_ident.to_string f.name))
		in bt_prod acc btarg)
	bt_body
	f.params
	
	

let env_find name envsig=
	if sig_exists name envsig.sign_ord then 
		let (_,var)=QNameMap.find name envsig.sign_ord
		in sigtype name var 
	else
		(* not signature *)
	try QNameMap.find name envsig.env_map with 
		Not_found -> (*not variable*)
		if QNameMap.mem name envsig.predmap 
		   then TBool (* predicate *)
		   else 
		 try 
			let fct=List.assoc name envsig.funclist in
		    bt_func fct
		 with Not_found -> (* not function *)
			TVarndef name


(* do the join with basesig in the environment, only for variables that work basesig*)
let joinsig name envirsig=
	let newmap=QNameMap.map (fun bt -> match bt with
		|TBool -> TBool
		|TVarndef n -> TVarndef n
		|TRel r -> let bt1=BoundType.map (fun (l,b)-> match l with
				|t::q-> if base_inter envirsig.sign_ord (Base_Sig name) t 
							then (q,b)
							else ([],b)
				| [] -> ([],b)) r
				in let newbt=TRel (BoundType.filter (fun (l,b)-> l<>[]) bt1)
				in bt_union (TRel r) newbt
				) envirsig.env_map
	(* security, should be useless *)
	in let finalmap=QNameMap.filter (fun x bt-> not (bt_isempty bt)) newmap
	in {envirsig with env_map=finalmap;}

(* tests including varndef *)
let if_form_then_else a x y=
	if bt_isform a then x
	else if bt_isvarndef a then return a
	else y
	
let if_rel_then_else a x y=
	if bt_isrel a then x
	else if bt_isvarndef a then return a
	else y
	

let if_int_then_else a x y=
	if bt_isrel a then (if bt_mem ([Base_INT],false) a || bt_mem ([Base_INT],true) a then x else y)
	else if bt_isvarndef a then return a
	else y
(* with 2 arguments *)
let if_forms_then_else a b x y=
	if bt_isform a && bt_isform b then x
	else if bt_isvarndef a then return a
	else if bt_isvarndef b then return b
	else y

(* same with relations *)
let if_rels_then_else a b x y=
	if bt_isrel a && bt_isrel b then x
	else if bt_isvarndef a then return a
	else if bt_isvarndef b then return b
	else y


(* test whether all expressions from a bloc are formulas*)
(* returns typeform if it's ok, type_varndef if it's encountered, and type_empty if a relational type is found *)
let rec allform bloc env=match bloc with
				|[] -> typeform
				|e::q -> (compute_bt e env) >>= fun bt ->
							if bt_isrel bt then type_empty
							else if bt_isvarndef bt then return bt
							else allform q env

and allform_def l list2env deflist env= match l with
									|[] -> typeform
									| e::q -> (list2env deflist env)>>= fun newenv ->
												compute_bt e newenv>>= fun bt ->
												if bt_isrel bt then type_empty
												else if bt_isvarndef bt then return bt
												else allform_def q list2env deflist env

and defs2env l env= match l with 
					|[]->return env
					| d::q-> (compute_bt d.expr env) >>= fun dtype -> 
							d.expr.typ <- Some dtype;
							let newenv={env with env_map=(env_add (Ast.Qname.local d.name) dtype env.env_map);}
							in defs2env q newenv

and decls2env l env=match l with 
						|[]->return env
						| d::q-> (compute_bt d.range env) >>= fun bt -> 
							 d.range.typ <- Some bt;
							  let dtype=bt_update_var bt d.is_variable in 
							  let newenv={env with env_map = List.fold_right (fun n m->env_add (Ast.Qname.local n) dtype m) d.names env.env_map;}
							  in decls2env q newenv						

(* hard-coded predicate for total order:
 pred/totalOrder[elem, first, succ] 
 produces an expression
 cur_expr is used for location and type
*)

and totpred elem first succ cur_expr=						
	(* debug *)
	let btstring=match first.typ with 
	|None -> "None"
	|Some bt->bt_to_string bt
	in
	Cfg.print_debug @@ Printf.sprintf "totalOrder/first type: %s\n" btstring;

	let x_id = Ast_ident.make (Fresh.fresh "elem_order")
	in
	let decl_x = {
		is_variable = false; (* warning: for now all total orders are constants, maybe to deal with later *)
		is_disjoint_variables = false;
		names = [x_id];
		range = elem;
		is_disjoint_ranges = false;
		}
	in
	let y_id = Ast_ident.make (Fresh.fresh "next_lone") in
	let decl_y = {
		is_variable = false; (* warning: for now all total orders are constants, maybe to deal with later *)
		is_disjoint_variables = false;
		names = [y_id];
		range = elem;
		is_disjoint_ranges = false;
		}
	in
	(*let z_id = Ast_ident.make (Fresh.fresh "next_unique") in
	let decl_z = {
		is_variable = false; (* warning: for now all total orders are constants, maybe to deal with later *)
		is_disjoint_variables = false;
		names = [z_id];
		range = elem;
		is_disjoint_ranges = false;
		}
	in*)
	
	let (x_expr:expr)=
		{first with expr=EQualName (Ast.Qname.local x_id)} in
	let (y_expr:expr)=
		{first with expr=EQualName (Ast.Qname.local y_id)} in
	(*let (z_expr:expr)=
		{first with expr=EQualName (Ast.Qname.local z_id)} in	
	let z_equal_y:expr=
		{cur_expr with expr=EComp(z_expr, CEq, y_expr)} in
	let z_in_xsucc:expr=
	    {cur_expr with expr=EComp(z_expr, CIn, xsucc)} in
	let zsucc_equal_y:expr=
		{cur_expr with expr=EBinary(z_in_xsucc, BImp, z_equal_y)} in
	let allz_equaly:expr=
		{cur_expr with expr=EQuant (`All, [decl_z], [zsucc_equal_y])} in*)
	
	let xsucc:expr=
		{first with expr=EBinary(x_expr, BDot, succ)} in
	let x_in_first:expr=
		{cur_expr with expr=EComp(x_expr, CIn, first)} in
	let one_first:expr=
		{cur_expr with expr=EQuant (`One, [decl_x], [x_in_first])} in
	let y_in_xsucc:expr=
	    {cur_expr with expr=EComp(y_expr, CIn, xsucc)} in
	let lone_xsucc:expr=
	    {cur_expr with expr=EQuant (`Lone, [decl_y], [y_in_xsucc])} in
	let succ_star:expr=
		{succ with expr=EUnary(UStar, succ)} in
	let reach_first:expr=
		{first with expr=EBinary(first, BDot, succ_star)} in
	let x_from_first:expr=
		{cur_expr with expr=EComp(x_expr, CIn, reach_first)} in
	let succ_hat:expr=
		{succ with expr=EUnary(UHat, succ)} in
	let reach_x:expr=
		{first with expr=EBinary(x_expr, BDot, succ_hat)} in
	let not_x_from_x:expr=
		{cur_expr with expr=EComp(x_expr, CNotIn, reach_x)} in
	let allx:expr=
		{cur_expr with expr=EQuant (`All, [decl_x], [lone_xsucc;x_from_first; not_x_from_x])} in
	{cur_expr with expr=EBinary (one_first,BAnd, allx)} 
		


(* computes the set of possible types of an Expression in Electrum, and variables are bounded to arities via the environment envar *)
and compute_bt electr_exp env_sig= 

	(* debug printing  *)
	let elecstring=
		(Util.PPrintX.to_string @@ Pretty.expr_to_document electr_exp) 
		^" at "^(Location.to_string electr_exp.loc)
		in
	(* print_endline @@ "Typing "^elecstring;*)
	let sigord=env_sig.sign_ord in
	(match electr_exp.expr with
  (* this *)
  | EThis -> (match env_sig.cursig with
			|None -> fail `ETyping (lazy ("'This' is not known in this context"^(Location.to_string electr_exp.loc)))
			|Some bt_this -> return bt_this
			)
  (* constants *)
  | EConst c -> (match c with 
		| CNum _ -> type_int
		| CNone -> type_univ (* None can match with anything *)
		| CIden -> type_univ_bin
		| CUniv -> type_univ
		| CInt -> type_int)
  (* let (local definition) *)
  | ELet (deflist, bloc) ->(match bloc with
						|[]->assert false
						|[e]-> (defs2env deflist env_sig)>>= fun newenv ->
									compute_bt e newenv
						| _::_ ->  (defs2env deflist env_sig)>>= fun newenv ->
									allform bloc newenv >>= fun bt->
										if_form_then_else bt
										(return bt)
										 (fail `ETyping (lazy ("Non-boolean expression appearing in a block"^(Location.to_string electr_exp.loc))))	      
						)
  (* quantified formulas *)
  | EQuant (quant, decl_list, bloc) ->  (match bloc with
								|[]->assert false
								| _::_ -> allform_def bloc decls2env decl_list env_sig>>= fun bt->
										if_form_then_else bt
										(return bt)
										(fail `ETyping (lazy ("Non-boolean expression appearing after a quantifier"^(Location.to_string electr_exp.loc)))) 
								)
  (* unary operator preceding an expression *)
  | EUnary (op,e) -> compute_bt e env_sig >>= fun etype -> (match op with 
    | UMinus -> if_int_then_else etype 
				 type_int 
				 (fail `ETyping (lazy ("Type Int Expected after Minus "^(Location.to_string electr_exp.loc))))
	| UNot -> if_form_then_else etype 
				typeform 
				(fail `ETyping (lazy ("Boolean Expression Expected after Not "^(Location.to_string electr_exp.loc))))
	| UQual _ -> if_rel_then_else etype
				typeform
				(fail `ETyping (lazy ("Relation expected after Qualifier "^(Location.to_string electr_exp.loc))))
	| UMult _ -> if_rel_then_else etype
				 (return etype )
				 (fail `ETyping (lazy ("Relation expected after Multiplicity "^(Location.to_string electr_exp.loc))))
	| UCard -> if_rel_then_else etype 
					type_int
					(fail `ETyping (lazy ("Wrong argument of Cardinal "^(Location.to_string electr_exp.loc))))
	| UTilde -> if_rel_then_else etype
				(let ar2=bt_filter (fun (l,b)->List.length l=2) etype in
				if bt_isempty ar2 then fail `ETyping (lazy ("~ can be used only with a binary relation."^(Location.to_string electr_exp.loc)))
							else return (apply_all 
							(fun (arg,v)->match arg with
							|[x;y]->[y;x],v
							|_ -> assert false)
							 ar2))
				(fail `ETyping (lazy ("~ can be used only with relations."^(Location.to_string electr_exp.loc))))
	 (*trans closure + id:univ->univ*)
	| UStar -> compute_bt {electr_exp with expr=EConst CIden;} env_sig >>= fun x->
				(compute_bt {electr_exp with expr=EUnary (UHat,e)} env_sig) >>= fun y ->
				 if_rels_then_else x y 
				 (return (bt_union x y))
				 (fail `ETyping (lazy ("Transitive Closure can be used only with relations."^(Location.to_string electr_exp.loc))))
	| UHat -> if_rel_then_else etype
				(let binrel=bt_filter (fun (l,b)->match l with 
												|[x;y]-> true 
												|_ -> false) 
												etype in
				if bt_isempty binrel then 
					(
					print_endline (bt_to_string etype);
					fail `ETyping (lazy ("^ can be used only with a binary relation of coherent type."^(Location.to_string electr_exp.loc)))
					)
				else 
				(* union with join until fixpoint *)
				return (bt_hat sigord binrel)
				)
				(fail `ETyping (lazy ("^ can be used only with relations."^(Location.to_string electr_exp.loc))))
	| UPrime -> if_rel_then_else etype
					(return etype)
					(fail `ETyping (lazy ("' cannot be used with a formula."^(Location.to_string electr_exp.loc))))
	| UAlways -> if_form_then_else etype
					typeform
					(fail `ETyping (lazy ("'always' must be used with a formula."^(Location.to_string electr_exp.loc))))
	| UEventually -> if_form_then_else etype
					typeform
					(fail `ETyping (lazy ("'eventually' must be used with a formula."^(Location.to_string electr_exp.loc))))
	| UNext -> if_form_then_else etype
					typeform
					(fail `ETyping (lazy ("'after' cannot be used with a formula."^(Location.to_string electr_exp.loc))))
	| UPrevious -> if_form_then_else etype
					typeform
					(fail `ETyping (lazy ("'previous' cannot be used with a formula."^(Location.to_string electr_exp.loc))))
	| UOnce -> if_form_then_else etype
					typeform
					(fail `ETyping (lazy ("'once' cannot be used with a formula."^(Location.to_string electr_exp.loc))))
	| UHist -> if_form_then_else etype
					typeform
					(fail `ETyping (lazy ("'historically' cannot be used with a formula."^(Location.to_string electr_exp.loc))))
	)
  (* binary operator *)
  | EBinary (e1,op,e2) -> compute_bt e1 env_sig >>= fun et1 -> 
						compute_bt e2 env_sig >>= fun et2 -> 
						let string_exprs= (bt_to_string et1)^" and "^(bt_to_string et2)^"\nAt "^(Location.to_string electr_exp.loc) in
						(match op with 
    (* logic *)
	| BOr -> if_forms_then_else et1 et2
				typeform
				(fail `ETyping (lazy ("'Or' must be used with boolean formulas."^string_exprs)))
	| BAnd -> if_forms_then_else et1 et2
			  typeform
			  (fail `ETyping (lazy ("'And' must be used with boolean formulas."^string_exprs)))
	| BImp -> if_forms_then_else et1 et2
			  typeform
			  (fail `ETyping (lazy ("=> must be used with boolean formulas."^string_exprs)))
	| BIff -> if_forms_then_else et1 et2
			  typeform
			  (fail `ETyping (lazy ("<=> must be used with boolean formulas."^string_exprs)))
	| BUntil -> if_forms_then_else et1 et2
			  typeform
			  (fail `ETyping (lazy ("'until' must be used with boolean formulas." ^ string_exprs)))
	| BSince -> if_forms_then_else et1 et2
			  typeform
			  (fail `ETyping (lazy ("'since' must be used with boolean formulas." ^ string_exprs)))
	(* set & relational operators *)
	| BUnion -> if_rels_then_else et1 et2
			 (return (bt_union et1 et2))
			 (fail `ETyping (lazy ("Union must be used with relations: "^string_exprs)))
	| BInter -> if_rels_then_else et1 et2
				(let bt_int=bt_inter sigord et1 et2 in 
					if bt_isempty bt_int then fail `ETyping (lazy ("Intersection always empty: "^string_exprs))
					else return bt_int
				)
				(fail `ETyping (lazy ("Intersection must be used with relations: "^string_exprs)))
	| BMinus -> if_rels_then_else et1 et2
			(return et1)
			(fail `ETyping (lazy ("Minus must be used with relations: "^string_exprs)))
	| BOver -> compute_bt {electr_exp with expr=EBinary (e1,BUnion,e2);} env_sig
	| BLProj -> if_rels_then_else et1 et2
				(let et1_f=bt_filter (fun (x,b)->List.length x=1) et1 in
				if bt_isempty et1_f then fail `ETyping (lazy ("Projection must use a set: "^string_exprs))
					else let filter_one (l,var)=(match l with
							|[x] -> let et2_f=bt_filter (function
															|[],b->assert false
															|yh::yq,b-> base_inter sigord x yh) et2 
									in apply_all (function
										|[],v ->assert false
										|b::q,v -> try (base_inter_type sigord x b)::q,v||var with Not_found -> assert false
										) et2_f
							|_ -> assert false )
					in  return (bt_fold_from_empty (fun x s->bt_union (filter_one x) s) et1_f)
				)
				(fail `ETyping (lazy ("Projection must be used with relations: "^string_exprs)))
	| BRProj -> if_rels_then_else et1 et2
					(let et2_f=bt_filter (fun (x,v)->List.length x=1) et2 in
					if bt_isempty et2_f then fail `ETyping (lazy ("Projection must use a set:"^string_exprs))
						else let filter_one (l,var)=(match l with (*TODO deal with var bool carefully*)
								|[x] -> let et1_f=bt_filter (fun (y,v)->match List.rev y with
															|[]->assert false
															|yh::yq-> base_inter sigord x yh) et1 
										in apply_all (fun (l2,v2)->
										(match List.rev l2 with
											|[] -> assert false
											|b::q -> try List.rev ((base_inter_type sigord x b)::q),v2 with Not_found ->assert false
											)
										) et1_f
								|_ -> assert false )
						in  return (bt_fold_from_empty (fun x s->bt_union (filter_one x) s) et2_f)
					)
					(fail `ETyping (lazy ("Projection must be used with relations: "^string_exprs)))
	| BDot -> if_rels_then_else et1 et2 
				(bt_join sigord (return et1) (return et2) >>= 
					fun btj -> if bt_isempty btj then 
					(fail `ETyping (lazy ("Empty Join: "^elecstring^": "^string_exprs^(envirsig_to_string env_sig))))
					 else return btj
				)
				(fail `ETyping (lazy ("Join must be used with relations: "^string_exprs)))
	)
	(*
	(* save the returned type *)
	>>= fun res_bt ->
	electr_exp.typ <- Some res_bt;
	return res_bt
	*)
  (* cartesian product with multiplicities à la UML *) (* multiplicities ignored for now *)
  | ECart (e1, m1, m2, e2) -> compute_bt e1 env_sig >>= fun et1 ->
								compute_bt e2 env_sig >>= fun et2 ->
								let string_exprs= (bt_to_string et1)^" and "^(bt_to_string et2)^"\nAt "^(Location.to_string electr_exp.loc) in
								if_rels_then_else et1 et2 
								(return (bt_prod et1 et2 ))
								(fail `ETyping (lazy ("Product must be used with relations: "^string_exprs)))
  (* comparison of expressions *)
  | EComp (e1, op, e2) -> compute_bt e1 env_sig >>= fun et1 ->
						  compute_bt e2 env_sig >>= fun et2 ->
						  let string_exprs= (bt_to_string et1)^" and "^(bt_to_string et2)^"\nAt "^(Location.to_string electr_exp.loc) in
								if_rels_then_else et1 et2 
									(let bt_int=bt_inter sigord et1 et2 in
									if bt_isempty bt_int then fail `ETyping (lazy ("Comparison between incompatible types: "^string_exprs))
									else typeform)
								(fail `ETyping (lazy ("Product must be used with relations: "^string_exprs)))
  (* ... implies ... else ... (no else == "else true") *)
  | EIte (e1,e2,e3) -> compute_bt e1 env_sig >>= fun et1 ->
					  compute_bt e2 env_sig >>= fun et2 ->
					  compute_bt e3 env_sig >>= fun et3->
						if bt_isform et1 then 
							(if_rels_then_else et2 et3) 
								(return (bt_union et2 et3))
								(if_forms_then_else et2 et3
									typeform
									(fail `ETyping (lazy ("IfThenElse must be used with two relations or two formulas."^"\nAt "^(Location.to_string electr_exp.loc)))))
							else
							if bt_isvarndef et1 then return et1 
						else
							(fail `ETyping (lazy ("IfThenElse must be used with formula condition."^"\nAt "^(Location.to_string electr_exp.loc))))
  (* function/relation/predicate application *)
  | EApp (f, expr_list) -> 
		let funcase ()= (* function/relation case *) 
			compute_bt f env_sig >>= fun ft ->
			f.typ <- Some ft;
			(* do it for all arguments *)
			let rec appl ef l=(match l with
				|[]->ef
				|e::q->compute_bt e env_sig >>= fun et ->
						e.typ<- Some et;
						appl (bt_eat sigord ef (return et) ) q)
			in appl (return ft) expr_list
		in (match f.expr with 
			(* try predicate *)
				| EQualName n->
				(* hardcoded pred/totalOrder *)
					if Ast.Qname.to_string n="pred/totalOrder" then
						match expr_list with
						|[elem;first;succ] ->
							let tot_expr=totpred elem first succ electr_exp in
							compute_bt tot_expr env_sig 
							(* careful : no type to the predicate name , because A*Bool is not allowed *)
						| _ -> 
							fail `ETyping (lazy ("Wrong arity of default predicate pred/totalOrder\nAt "^(Location.to_string electr_exp.loc)))
					else
						(try let plist= env_find_list n env_sig.predmap in		
						let rec check l1 l2=(match (l1,l2) with
							|([],[])-> typeform
							|([], _) -> fail `ETyping (lazy ("Wrong arity of predicate "^(Ast_qname.to_string n)^"\nAt "^(Location.to_string electr_exp.loc)))
							|(_,[]) -> fail `ETyping (lazy ("Wrong arity of predicate "^(Ast_qname.to_string n)^"\nAt "^(Location.to_string electr_exp.loc)))
							|(e::q1, t::q2)->compute_bt e env_sig>>= fun et->
									let intertype=bt_inter sigord et t in
									if bt_isvarndef intertype then return intertype else
										if bt_isempty intertype 
										then fail `ETyping (lazy (
											"Wrong type in argument of "^(Ast_qname.to_string n)^": "
											^(bt_to_string et)^" instead of "^(bt_to_string t)
											^"\nAt "^(Location.to_string electr_exp.loc)^"\n"^(envirsig_to_string env_sig)))
										else check q1 q2 
							)
						in check expr_list plist
						with Not_found -> funcase())
				| _ -> funcase() )
							
  (* ident prefixed by '@': ident shouldn't be dereferenced *)
  (* we do the product with the signature where it is defined *)
  | EAtName n->	
		(* we compute the signature where it is defined *)
		(try 
		let (qn_list, signature)=
			List.find
			(fun (_, s)-> List.exists 
				(fun (field:decl) -> List.mem n field.names) s.fields
			)
			env_sig.sig_list
		in
		let sigdef=List.hd qn_list in
		let bt_def=sigtype sigdef signature.is_variable in
		let expr_name={electr_exp
				 with expr=EQualName (Ast_qname.local n)}
		in
		compute_bt expr_name env_sig>>= fun bt_name ->
		return (bt_prod bt_def bt_name)
		with Not_found -> type_varndef (Ast_qname.local n)
		)
  (* qualified name *)
  | EQualName n -> 
		let bt=env_find n env_sig in
		if bt_isform bt then 
			let btlist= env_find_list n env_sig.predmap in
			(match btlist with 
			|[] -> typeform
			|[x] when bt_isvarndef x-> return x
			| _ ->
				fail `ETyping (lazy ("Arguments must be used with predicate "
				^ (Ast_qname.to_string n)^": "
				^ "\nAt "^(Location.to_string electr_exp.loc)))
			)
		else  
		return bt
  (* block = possibly-empty list of expressions  *)
  | EBlock bloc -> (match bloc with
						|[]-> typeform (* we assume that an empty list means "True" *)
						|[e]-> compute_bt e env_sig 
						| _::_ -> allform bloc env_sig >>= fun bt->
							if bt_isrel bt then fail `ETyping (lazy ("Non-formula appearing in a block:\nAt " 
												 ^ Location.to_string electr_exp.loc))
							else return bt
						)
  (* relation defined by comprehension *)
  | ECompr (decl_list , block)  -> (* to change: the type of the set is the product of the computed types *)
				let rec decls2env_bt l env=(match l with 
					|[]->return (env,bt_empty)
					| d::q-> compute_bt d.range env >>= fun bt -> 
							  let dtype=bt_update_var bt d.is_variable in 
								let newenvmap=List.fold_right (fun n m->env_add (Ast.Qname.local n) dtype m) d.names env.env_map in 
								let dtypemult=List.fold_left (fun accmult x ->bt_prod dtype accmult) bt_empty d.names  in
								let newenv={env with env_map=newenvmap;sign_ord=sigord;} in
								decls2env_bt q newenv >>= fun (finalenv,finaltype)->
								if_rels_then_else dtypemult finaltype
									(return (bt_prod dtypemult finaltype))
									(fail `ETyping (lazy ("Non-formula expression appearing as comprehension condition.\nAt "^(Location.to_string electr_exp.loc))))
								(*print_endline ("prodtype:"^(bt_to_string prodtype));*)
								>>= fun prodtype ->
								return (finalenv,prodtype))
				in (match block with
					|[]->assert false
					| _::_ -> decls2env_bt decl_list env_sig >>= fun (newenv,newtype)->
							 allform_def block decls2env decl_list newenv >>= fun bt -> 
							 if bt_isrel bt then fail `ETyping (lazy "Non-formula expression appearing as comprehension condition")
							 else if bt_isvarndef bt then return bt
							 else return newtype
					)
	)
	>>= fun result ->
	
	(*(if not (bt_isvarndef result) then  *)
	if not (bt_isempty result) then 
	(electr_exp.typ<-Some result; 
	(* debug *)
	if bt_ismixed result
		then Cfg.print_debug (Printf.sprintf "%s has mix-type %s\n" elecstring (bt_to_string result)); 
	);
	return result
				

(*for debugging purposes *)
let print_par (p:Ast_par.paragraph)= match p with 
  |Sig s -> print_endline ("Sig:"^(Ast_ident.to_string (List.hd s.names)))
  | Enum e -> print_endline "Enum"
  | Fact f -> print_endline "Fact"
  | Pred p -> print_endline ("Pred "^(Ast_ident.to_string p.name))
  | Fun f -> print_endline ("Fun "^(Ast_ident.to_string f.name))
  | Assert a -> print_endline "Assert"

let print_iplist l=let f x=match x with
	|(Imp i)-> ()
	|(Parag p) -> print_par p
	in List.iter f l


(* auxiliary function, computing an environment and a list of argument types from a list of declarations *)
let rec decls2env_list l env acclist=(match l with 
						|[]->return (env,acclist)
						| d::q-> (compute_bt d.range env) >>= fun bt -> 
							  d.range.typ <- Some bt;
							  let dtype=bt_update_var bt d.is_variable in 
							  let dtypemult=List.map (fun x ->dtype) d.names  in
							  let newenv={env with env_map = List.fold_right (fun n m->env_add (Ast.Qname.local n) dtype m) d.names env.env_map;}
							  in decls2env_list q newenv (acclist@dtypemult))			

(* remove commands in a par_cmd list, and change Par to Parag for concatnation with Imp list *)
let rm_cmd par_cmd_list= 
	let l = List.filter (fun x -> match x with Par _ -> true | Cmd _ -> false ) par_cmd_list
	in 
	let par_list=List.map (function (Par p)-> Parag p | Cmd _ -> assert false ) l in
	let l2=List.filter (fun x -> match x with Par _ -> false | Cmd _ -> true ) par_cmd_list  in
	let cmd_list=List.map (function (Par _)-> assert false | Cmd c -> c ) l2 in
	par_list,cmd_list


(* (X,[A,B,C]) means "abstract sig X { } one sig A, B, C extends X { }"*) 
let enum_to_siglist (e:Ast_par.enum)=
  let main_sig=[Ast_qname.local e.name], {
	is_variable = false; (* warning: no syntax for is_variable in enum *)
	is_abstract = true;
	mult = None;
	names = [e.name];
	extends = None;
	fields = [];
	fact = None;
	}
  in 
  let subsig=List.map Ast_qname.local e.cases,
	{
	is_variable = false;
	is_abstract = false;
	mult = None;
	names = e.cases;
	extends = Some (Extends (Ast_qname.local e.name));
	fields = [];
	fact = None;
	} 
 in [main_sig; subsig]

(* compute the local fields of a signature, using sign_ord and siglist of an environment *)
let extend_fields sig_qname env=
	let (bigsigs_set,_)=QNameMap.find sig_qname env.sign_ord in
	QNameSet.fold 
		(fun s acc->
			let (_,signature)=
				List.find (fun (l,_)-> List.mem s l) env.sig_list
			in signature.fields@acc)
		bigsigs_set 
		[]

(* this processes an imported file and returns the computed environment*)
let rec process_import ?(debug=Some false) mod_name params=
			let ast= Parser_main.parse (!Cfg.alloyfolder^(Ast_qname.to_string mod_name)^Cfg.extension) (* add debug ? *) in
			let treat (mod_decl_opt,imp_list,par_cmd_list) =
			(* remove commands and add imports*)
			(* commands in imported modules are ignored *)
				let (par_list, _ )=rm_cmd par_cmd_list in
				let imp_par_list=List.fold_left (fun acc i -> (Imp i)::acc) par_list imp_list in 
			(* replace names of parameters *)
				(match mod_decl_opt with 
					|None -> if params=[] then return imp_par_list else fail `ETyping (lazy "Empty argument in module call")
					|Some (name, args) -> (try return (List.fold_left2 (fun acc x v -> replace_iplist x v acc) imp_par_list args params)
						with Invalid_argument list -> fail `ETyping (lazy "Wrong number of arguments in module call"))
				)
				>>= fun newlist-> 
				process_file newlist params>>= fun newenv ->
				(* remove signatures given in parameters in the computed environments *)
				return (siglist_remove params newenv)
			in
			handle ~f:treat ast
			~handle:(fun x s -> Printf.eprintf "%s\n%!" s; return empty_envir) (* TODO deal properly : we now remove parsing errors *)


(* the function process_file take a file and a list of parameters, which are signatures supposed to exist *)
(* it returns a full environment *)
and process_file par_cmd_list args=
	(* add the new signatures given as arguments, as static signatures *)
	(* TODO: enrich formal arguments with is_variable *)
	let newsig= addsiglist args [] false empty_envir.sign_ord in
	process_file_pass par_cmd_list {empty_envir with sign_ord=newsig;}>>= 
	fun first_pass ->
	(* make several passes until the remaining field of environment is empty *)
	let rec pass env = let rem = nb_remain env in
						if rem = 0 && env.facts_typed then return env 
						else
						(
						process_file_pass par_cmd_list (purge env) >>= fun newenv ->
						let n=nb_remain newenv in
						if n>=rem (* no new variable identified *)
							then 
							try let nondef_qname= some_remain env in
									fail `ETyping (lazy (
									"Unknown name : "^(Ast_qname.to_string nondef_qname)^"\n"
									^(string_of_int n^" in total\n")^(envirsig_to_string env)))
							with Not_found -> (* print_endline "\n\n\n\nNo new name and no nondef remaining.....\n\n\n"; *)
									if n=0 && newenv.last_try then pass {newenv with last_try=false} (* some facts have not been typed, we do another pass *)
									else fail `ETyping (lazy ( "Some facts cannot be typed" ))
									
							else pass newenv
						)
	in pass first_pass
	

(* to call when the blocks of the file are sorted by dependency *)
and process_file_pass blocs acc_env=let open Ast_par in match blocs with	
	  |[] -> return acc_env
	  |(Imp (mod_name, params, alias_opt))::q ->
		    let alias=(match alias_opt with
			        |None-> Ast.Qname.local (Ast_ident.make "")
			        |Some iden -> Ast.Qname.local iden)
				in process_import mod_name params
				(* Careful, convention different from Alloy *)
				>>= fun newenv-> process_file_pass q (env_concat_pref acc_env alias newenv params)
	  |(Parag p)::q -> (match p with 
	        |Sig s -> 
	    	      let newsig= (*new signatures environment containing names of s and their extensions *)
				        let namelist= List.map Ast.Qname.local s.names in
				        (match s.extends with
				          |Some (Extends extname) -> addsiglist namelist [extname] s.is_variable acc_env.sign_ord
				          |Some (In extlist) -> addsiglist namelist extlist s.is_variable acc_env.sign_ord
				          |None -> addsiglist namelist [] s.is_variable acc_env.sign_ord)
			        in
			        let env_f={acc_env with sign_ord=newsig;} in
			        let treat_one_name idname_sig=	
				        let qname_sig=Ast.Qname.local idname_sig in
				        let add_id id bt envinit= (*add a list of identifiers in environment *)
					        let newmap=env_add (Ast.Qname.local id) bt envinit.env_map
					        in
					        {envinit with env_map=newmap;}
				        in 
				        let add_decl dec env globalenv= (*add a declaration in local environment envmap, with globalenv in the background*)
					        (* careful :  we might extend another signature and use its local fields *)
					        let totalenv= {globalenv with 
						                       env_map=envir_union_back env.env_map globalenv.env_map;
						                       cursig=Some (sigtype (qname_sig) s.is_variable);
						                    }

					        in
					        compute_bt dec.range totalenv >>= fun bt-> 
					        let newbt=bt_addvar bt dec.is_variable in
					        return (List.fold_right 
						                (fun n env2->add_id n newbt env2)
						                dec.names env)
				        in
				        let locfields= (extend_fields qname_sig env_f) @ s.fields  in
				        (* add the local fields types to environment*)
				        List.fold_left
				          (fun env_fault dec-> env_fault >>= fun env ->
				            add_decl dec env env_f)
				          (return empty_envir) locfields 
				        >>= fun localenv->

				        (* add localenv prefixed with the signature name *)
				        let newenvmap=envir_union 
						                    (add_first_col qname_sig localenv.env_map) 
						                    acc_env.env_map
				        in				

				        (* check the local fact in ext_env+localenv *)
				        let semiloc_env={env_f with
						                       env_map=envir_union_back localenv.env_map  acc_env.env_map;
						                       cursig=	Some (sigtype (qname_sig) s.is_variable);
						                    }
				        in
				        (match s.fact with
					        |None-> typeform
					        |Some bloc -> allform bloc semiloc_env)
				        >>= fun fact_type ->
				        if bt_isrel fact_type then 
					        fail `ETyping (lazy "Local fact is not a boolean") 
				        else
				          let new_bool=
					          if bt_isvarndef fact_type 
						        then (
						          (* debug 
						             Printf.eprintf "Failure to type %s in signature %s\n: %s\n" 
							           (Ast_qname.to_string @@ bt_remain fact_type )
							           (Ast_ident.to_string @@ List.hd s.names)
							           (envirsig_to_string semiloc_env)
							           ;*)
							        false
							      )
						        else acc_env.facts_typed 
				          in

				          return {env_f with 
					                  env_map=newenvmap;
					                  facts_typed=new_bool;
					               }
			        in
			        List.fold_left 
				        (fun accf qn -> accf>>= fun acc->
					        treat_one_name qn >>= fun newenv->
					        return {acc with 
						                env_map=envir_union newenv.env_map acc.env_map;
						                facts_typed=newenv.facts_typed && acc.facts_typed}
				        ) (return env_f) s.names
			        >>= fun sigenv->
			        process_file_pass q {sigenv with 					
					                           sig_list= update_sigs 
						                                     (List.map Ast_qname.local s.names,s)
						                                     env_f.sig_list;}

		      | Enum e -> (* (X,[A,B,C]) means "abstract sig X { } one sig A, B, C extends X { }"*) 
					    let newsig=addsiglist 
						               (List.map Ast.Qname.local e.cases)
						               [Ast.Qname.local e.name]
						               false (* no is_variable field, interpreted as static by default *)
						               acc_env.sign_ord

					    in process_file_pass q {acc_env 
						                          with sign_ord=newsig;
						                               sig_list=acc_env.sig_list@(enum_to_siglist e)}
		      | Fact f -> 	allform f.body acc_env >>= fun bt ->
			        if bt_isrel bt then
                fail `ETyping @@
                lazy ("Non-formula stated as a fact:\n"
                      ^ (Util.PPrintX.to_string @@ Pretty.fact_to_document f))
              else
						    let boolfact=acc_env.facts_typed && bt_isform bt in
						    (*else if bt_isvarndef bt then 
							    let n=bt_remain bt in 
							    (*remember that something is undefined *)
							    type_varndef n>>= fun bt_ndef -> 

							    let newenv={acc_env with env_map=env_add n bt_ndef acc_env.env_map} in
							    process_file_pass q newenv *)
						    process_file_pass q {acc_env with
							                         factlist=
								                         if List.mem f acc_env.factlist then acc_env.factlist
								                         else f::acc_env.factlist;
							                         facts_typed=boolfact;
							                      }

		      | Pred p -> decls2env_list p.params acc_env []>>= fun (newenv,parlist)->
					    allform p.body newenv >>= fun bt ->
					    (* if we cannot type the predicate we remember why *)
					    let predtype=if bt_isvarndef bt then [bt] else parlist in
					    let newpred=map_add (Ast.Qname.local p.name) predtype acc_env.predmap in
					    if bt_isrel bt then fail `ETyping (lazy (
						        "Non-formula stated in predicate " 
						        ^ (Ast_ident.to_string p.name)^".\n"
					        ))
					    else 
					      (* let boolfact=acc_env.facts_typed && bt_isform bt in *)
					      process_file_pass q {acc_env with 
						                           predmap=newpred;
						                           predicates=map_add (Ast.Qname.local p.name) p acc_env.predicates;
						                           (*facts_typed=boolfact;*)
						                        }

		      | Fun f ->  (* f will be treated as a variable, and put in the normal environment *)
			        decls2env_list f.params acc_env []>>= fun (newenv,arglist) ->
			        compute_bt f.body newenv >>= fun body_type ->
			        f.body.typ <- Some body_type;
			        compute_bt f.returns newenv >>= fun return_type ->
			        f.returns.typ <- Some return_type;
			        if not @@ bt_incl acc_env.sign_ord body_type return_type
			        then (
				        print_endline ("WARNING: return type "^(bt_to_string return_type)^
								               "\ndoes not match computed type "^(bt_to_string body_type)^
								               "\nin function "^(Ast_ident.to_string f.name)));
				      let finaltype=bt_prod (List.fold_left bt_prod bt_empty arglist) return_type in
				      let fname=Ast.Qname.local f.name in
				      let finalenv=env_add fname finaltype acc_env.env_map in
				      let newfunlist=
					      if List.mem (fname,f) acc_env.funclist 
					      then acc_env.funclist
					      else (fname,f)::acc_env.funclist;
				      in
				      process_file_pass q {acc_env with
					                           env_map=finalenv;
					                           funclist=newfunlist;
					                        }

		      | Assert a -> allform a.body acc_env >>= fun bt ->
						  if bt_isrel bt then 
						    fail `ETyping (lazy ("Non-formula expression stated in assertion"
							                       ^ 
							                       (match a.name with
								                       |Some id-> " "^(Ast_ident.to_string id)^".\n"
								                       |None -> ".\n"
							                       )))
						  else 
						    let boolfact= acc_env.facts_typed && bt_isform bt in
						    let aslist=
							    if List.mem a acc_env.assertlist then acc_env.assertlist
							    else a::acc_env.assertlist
						    in
						    process_file_pass q {acc_env with
							                         assertlist=aslist;
							                         facts_typed=boolfact;}
		    )

	

let rec type_commands cmd_list env=
	match cmd_list with
	|[] -> ()
	|cmd::q -> (match cmd with
		| NamedCmd _ -> type_commands q env (* we ignore the named commands *)
		| BlockCmd (bloc, _ , _ ,_ ) -> 
			let bt_typ e= let _ = compute_bt e env in () in
			List.iter bt_typ bloc;
			type_commands q env
		)
		
	
(* process the root file *)
let process_root (mod_decl_opt,imp_list,par_cmd_list)=
	let (par_list, cmd_list)=rm_cmd par_cmd_list in (* separate commands from the rest *)
	(* add the imports *)
	let imp_par_list=List.fold_left (fun acc i -> (Imp i)::acc) par_list imp_list in 
	(*for now we also add the signatures declared as arguments of the modules as paragraphs *)
	let params=(match mod_decl_opt with
		|Some (name,args)-> args
		|None -> [] 
		) 
	in
	process_file imp_par_list params >>= fun envtot ->
	(* we type the cmd_list *)
	type_commands cmd_list envtot;
	return {envtot with cmdlist=cmd_list} (* we finally add the cmd list *)


