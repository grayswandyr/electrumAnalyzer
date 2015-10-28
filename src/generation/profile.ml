(*******************************************************************************
 * Time-stamp: <2015-10-16 CEST 15:42:17 David Chemouil>
 * 
 * Electrum Analyzer 
 * Copyright (C) 2014-2015 Onera
 * Authors: 
 *   Denis Kuperberg <denis DOT kuperberg AT gmail DOT com>
 *   David Chemouil <david DOT chemouil AT onera DOT fr>
 *   Julien Brunel <julien DOT brunel AT onera DOT fr> 
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

(* profile - a profile is a type at the Electrum kernel level *)

open Batteries
open Util
open Names
open Types
open List

module Range = struct
(* a range is *one* list of (sort!) names representing the definition domains of
   a relation *)
  type t = name list
  let compare = List.compare Names.compare

  let print out sl =
    List.print ~first:"" ~last:"" ~sep:"×" String.print out sl

  let to_string set =
    BatIO.to_string print set
end

type range = Range.t


(* a profile is a set of ranges, as one may build unions of relations and also
   overload relations (yielding a union, internally) *)
module U = Set.Make (Range)

module Union = struct
  include U
  let print out set =
    U.print ~first:"{" ~last:"}" ~sep:"; "  Range.print out set

  let to_string set =
    BatIO.to_string print set
end

type t = Union.t

(* partial order on signatures *)
module NameMap = Map.Make(struct type t = name let compare = Names.compare end)

(* a signature is mapped to the signatures bigger than itself *)
module NameSet = Set.Make(struct type t=name let compare = Names.compare end)

(* equivalence classes of signatures *)
module EqClasses= Set.Make(struct type t=NameSet.t let compare = NameSet.compare end)

(* the second component gives the Equivalence classes of disjoint signatures (brothers in extends) *)
(* bool = true => the signature is variable *)
type signame_order = ((NameSet.t * bool) NameMap.t) * EqClasses.t

(* environment bounding a boolean (true => exactly) and a integer
   bound to a sort name *)
type typescopes = (bool * int) NameMap.t


type signame_mult = (Ast_expr.some_lone_one option) NameMap.t 
(* environment that consists of an ordering between signatures and a bounding environment *)
type sig_env = 
    { sigord : signame_order ;
      sigbounds : typescopes ;
      sigmult : signame_mult ;
      abstract_sigs : name list ;
    }

let mult_is_one sigenv s =
  try
    match (NameMap.find s sigenv.sigmult)	    
    with
    | Some `One  -> true
    |_ -> false
  with
    Not_found ->
    failwith ("Profile:mult_is_one: signature " ^ s ^ " not found.")

(* idem as mult_is_one but the first paramter is of type signame_mult *)
let mult_is_one2 sigmult s =
  try
    match (NameMap.find s sigmult)	    
    with
    | Some `One  -> true
    |_ -> false
  with
    Not_found ->
    failwith ("Profile:mult_is_one2: signature " ^ s ^ " not found.")

  
let mult_is_one_or_some2 sigmult s =
  try
    match (NameMap.find s sigmult)	    
    with
    | Some `One | Some `Some  -> true
    |_ -> false
  with
    Not_found ->
    failwith ("Profile:mult_is_one_or_some2: signature " ^ s ^ " not found.")


let mult_is_one_or_lone sigenv s =
  try
    match (NameMap.find s sigenv.sigmult)	    
    with
    | Some `One | Some `Lone -> true
    |_ -> false
  with
    Not_found -> failwith ("Profile:mult_is_one_or_lone: signature " ^ s ^ " not found.")

(* idem as mult_is_one_or_lone but the first parameter is of type signame_mult *)
let mult_is_one_or_lone2 sigmult s =
  try
    match (NameMap.find s sigmult)	    
    with
    | Some `One | Some `Lone -> true
    |_ -> false
  with
    Not_found -> failwith ("Profile:mult_is_one_or_lone2: signature " ^ s ^ " not found.")


let default_bounds sigmult siglist =
  List.fold_right
    (fun x y ->
     (* if sig is a one sig then we add mult exactly one *)
     if mult_is_one2 sigmult x
     then
       NameMap.add x (true, 1) y
     else
       (* if sig is a lone sig then we add mult not exactly one *)
       if mult_is_one_or_lone2 sigmult x
       then
	 NameMap.add x (false, 1) y
       (* else we add the mult by default *)
       else
	 NameMap.add x (false, 3) y
    )
    siglist
    NameMap.empty

    
 
let print_bound bnd =
  NameMap.print BatString.print (Tuple2.print Bool.print Int.print)
     		stdout bnd

let print_signame_order sigord = 
  NameMap.print BatString.print (Tuple2.print (NameSet.print BatString.print) Bool.print) 
		stdout
		(fst sigord);flush (stdout)

(* from Ident QualName to Name *)
let id_to_name id= Names.make (Ast.Ident.to_string id)
let qn_to_name qname= Names.make (Ast_qname.to_string qname)


(* from name back to qname *)
let name_to_qn name= 
	let pathlist=BatString.nsplit name "/" in
	let rec isolate= function
		|[] -> failwith "name_to_qn: empty name"
		|[n] -> ([], Ast_ident.make n)
		|t::q ->  let (path, id)=isolate q in 
			((Ast_ident.make t)::path, id)
	in
	let (path, idname)=isolate pathlist in
	Ast_qname.make false path idname

(*retrieve the path from path_info, which is a of the form a/b/c/d  (d is irrelevant) *)
let name_to_qn_path name path_info= 
  let idname=Ast_ident.make name in 
  try
	(* remove last id in path_info *)
	let (path,_)=BatString.rsplit path_info "/" in
	(* get the path as list of strings *)
	let pathlist=BatString.nsplit path "/" in
	let idlist=List.map Ast_ident.make pathlist in
	Ast_qname.make false idlist idname
   with Not_found -> (* no "/" in path_info *)
		Ast_qname.local (Ast_ident.make name)

(* change a qnamemap to a namemap *)
let qnmap_to_namemap qnmap=
	let enum = QNameMap.enum qnmap in
	let enum2= BatEnum.map (fun (a,b)-> (qn_to_name a, b)) enum in
	NameMap.of_enum enum2


(*changes the qnames in names in the signature 
*)
let base_toname base= match base with
	| Base_INT -> int
	| Base_UNIV -> univ
	| Base_Sig qname -> qn_to_name qname
	| Base_Ndef qname -> failwith "Undefined signature"

let sigord_toname sigord =
  let order = 
    QNameMap.fold 
      (fun base (set,b) accmap -> (* b is the boolean for 'dynamic' *)
       let nbase = qn_to_name base in
       let nset = QNameSet.fold 
		    (fun x acc-> NameSet.add (qn_to_name x) acc)
		    set NameSet.empty
       in
       NameMap.add nbase (nset,b) accmap)
      sigord NameMap.empty
  in
  let classes = EqClasses.empty
  in
  order , classes

(* is s included in t ?*)
let sort_incl (sigord, _) s t=
		let (set,b)= try (NameMap.find s sigord)
		with Not_found -> failwith ("Sort_inclusion: Sort "^s^" not found")
		in s=t || NameSet.mem t set

(* are we sure two sorts don't overlap *)
let sorts_are_disjoint sigord_tot s t =
	let (sigord, classes) = sigord_tot in 
	(* do they have parents of the same class ? *)
	let rep=
	EqClasses.exists 
		(fun set -> 
		   (* exists x,y in set, so disjoint *)
			 NameSet.exists (fun x->
			       NameSet.exists (fun y->
				           (* s in x and t in y *)
				           sort_incl sigord_tot s x && sort_incl sigord_tot t y && x <> y
			           ) set
			     ) set
	  ) classes
	  in 
	  (* if rep then Cfg.print_debug (s^" and "^t^" are disjoint\n"); *)
	  rep
  (* |> tap (fun res -> Cfg.print_debug *)
  (*         @@ Printf.sprintf "sorts_are_disjoint %s %s: return %B\n%!" *)
  (*              s t res) *)
 

 
(* are two sort intersecting ? *)

let sort_inter sigord_tot s t =
	let (sigord, classes) = sigord_tot in 
	let incl=
	  if s=t then true 
	  else
		(* i in s and t *)
		NameMap.exists (fun i (big,b) -> 
			(s=i || NameSet.mem s big)
			&& (t=i || NameSet.mem t big))
			sigord
		(* s and t in i *) 
		||
		let (bigs,_)=NameMap.find s sigord in
		let (bigt,_)=NameMap.find t sigord in
		NameMap.exists (fun i (big,b) -> 
			(s=i || NameSet.mem i bigs)
			&& (t=i || NameSet.mem i bigt))
			sigord
	in 
        let disj= sorts_are_disjoint sigord_tot s t in 
        let rep = incl && not disj in
	(* let aux=if rep then " " else " do not " in  *)
        (* Cfg.print_debug (s^" and "^t^aux^"intersect\n"); *)
	rep

(* true iff the sort s is variable *)
let is_var sigenv s =
  let var = 
    try 
      snd (NameMap.find s (fst sigenv.sigord))
    with
      Not_found -> failwith ("is_var: cannot find sort "^s^" in the signture ordering environment")
  in
  var

(* idem as is_var, but with paramater sigord *)
let is_var2 sigord s =
  let var = 
    try 
      snd (NameMap.find s (fst sigord))
    with
      Not_found -> failwith ("is_var2: cannot find sort "^s^" in the signture ordering environment")
  in
  var


 (* returns true iff the signature s is primary, i.e., s is not univ and s is not included 
     in another signature (except univ)*)
let is_primary sigenv s =
  if s = Names.univ || s = Names.empty then false
  else
    let (greater_sigs, _ ) = 
      try NameMap.find s (fst sigenv.sigord)
      with Not_found -> failwith ("Profile: is_primary: Sort " ^ s ^ " not found.\n") 
    in
    NameSet.equal greater_sigs (NameSet.add "univ" NameSet.empty)
    || NameSet.equal greater_sigs (NameSet.empty)

 (* idem as is_primary, but the first argment is a signame_order*)
let is_primary2 sigord s =
  if s = Names.univ || s = Names.empty then false
  else
    let (greater_sigs, _ ) = 
      try NameMap.find s (fst sigord)
      with Not_found -> failwith ("Profile: is_primary2: Sort " ^ s ^ " not found.\n") 
    in
    NameSet.equal greater_sigs (NameSet.add "univ" NameSet.empty)
    || NameSet.equal greater_sigs (NameSet.empty)

 (* finds the primary sig in which s is included *)
let primary_sig_of sigenv s =
  if (is_primary sigenv s) ||  s = Names.univ then 
    s
  else
    try
      let (s_greater_sigs, _) = NameMap.find s (fst sigenv.sigord) in
      NameSet.filter (is_primary sigenv) s_greater_sigs 
      |> NameSet.choose
    with
      Not_found -> failwith ("profile.ml: primary_sig_of: cannot compute primary sig of " ^ s)


(* finds the primary sig in which a sig s is included, *if it is
   variable* *)
let primary_sig_of_if_var_sig sigenv s =
  if is_var sigenv s then
	  primary_sig_of sigenv s
	else
	  s


 (* idem as primary_sig_of, but the first argument is a signame_order *)
let primary_sig_of2 sigord s =
  if (is_primary2 sigord s) ||  s = Names.univ then 
    s
  else
    try
      let (s_greater_sigs, _) = NameMap.find s (fst sigord) in
      NameSet.filter (is_primary2 sigord) s_greater_sigs 
      |> NameSet.choose
    with
      Not_found -> failwith ("profile.ml: primary_sig_o2f: cannot compute primary sig of " ^ s)
			    
(*  is a signature the direct super signature (in terms of extends or in) of another *)
let is_father sigenv son father =
  not (is_primary sigenv son)
  && 
    let (greater_than_son, _) = NameMap.find son (fst sigenv.sigord) in
    let (greater_than_father, _) = NameMap.find father (fst sigenv.sigord) in
    NameSet.mem father greater_than_son
  && NameSet.equal greater_than_father (NameSet.remove father greater_than_son)

(*  idem as is_father, but take an argument of type  signame_order *)
let is_father2 sigord son father =
  not (is_primary2 sigord son)
  && 
    let (greater_than_son, _) = NameMap.find son (fst sigord) in
    let (greater_than_father, _) = NameMap.find father (fst sigord) in
    NameSet.mem father greater_than_son
  && NameSet.equal greater_than_father (NameSet.remove father greater_than_son)
	
(* is a signatue the direct super signature (in terms of extends) of another *)
let is_father_for_extends sigord son father =
  is_father2 sigord son father
  (*son is present in some equivalence class, i.e., son extends some signature*)
  && EqClasses.exists 
       (fun set -> NameSet.mem son set)
       (snd sigord)

(* is a signatue the direct super signature (in terms of in) of another *)
let is_father_for_in sigord son father =
  is_father2 sigord son father
  (*son is not present in some equivalence class, i.e., son does not extend some signature*)
  && not (EqClasses.exists 
            (fun set -> NameSet.mem son set)
            (snd sigord))


(* find the direct super signature of a signature *)
let direct_super_sig sigenv s =
  let (greater_sigs, _ ) = 
      try NameMap.find s (fst sigenv.sigord)
      with Not_found -> failwith ("direct_super_sig: Sort " ^ s ^ " not found.\n") 
  in
  let set_father = NameSet.filter (is_father sigenv s) greater_sigs in
  try NameSet.choose set_father
  with
    Not_found -> failwith ("direct_super_sig: Sort " ^ s ^ " has no direct super sig.\n")
			  
(* add static hulls to primary var sigs *)
(* let bound_hulls sigenv= *)
(*    let newbounds= *)
(*    NameMap.fold *)
(* 		(fun s bound accmap ->  *)
(* 			let bound2=  *)
(* 				if Names.is_hull s *)
(* 				then  *)
(* 				  let varsig=Names.from_hull s in *)
(* 				  let (_,i)= try NameMap.find varsig sigenv.sigbounds  *)
(* 					with Not_found -> failwith ("bound_hulls: '"^varsig^"' not found") *)
(* 					in *)
(* 				  (true, i) (\* exactly i *\) *)
(* 				else bound  *)
(* 			in *)
(* 			NameMap.add	s bound2 accmap) *)
(* 		sigenv.sigbounds *)
(* 		NameMap.empty *)
(*   in *)
(*   {sigenv with sigbounds=newbounds;} *)
			
  
	
  
  

let sort_inter_type sigord_tot s t=
	(* we assume sort_inter s t*)
	let (sigord, _) = sigord_tot in 
	if s=t then s
	  else
		let (maxtype,_)=
		 try NameMap.choose 
		 (NameMap.filter 
		  (fun i (bigi,_) -> 
			(s=i || NameSet.mem s bigi)
			&& (t=i || NameSet.mem t bigi)
			(* maximality *)
			&& (let bigger=
				  NameMap.exists (fun j (bigj,_) -> 
					(s=j || NameSet.mem s bigj)
					&& (t=j || NameSet.mem t bigj)
					&& (NameSet.mem j bigi)
					&& (i <> j)) sigord
				in not bigger)
			)
		  sigord)
		  with Not_found -> failwith "Error in sort_inter_type"
		in 
		Cfg.print_debug (s^ " inter "^t^" = "^maxtype^"\n");
		maxtype
                                     
(* is range r1 included pointwise in r2 *)
let range_incl sigord_tot r1 r2 =
  List.for_all2 (fun s1 s2 -> sort_incl sigord_tot s1 s2) r1 r2


(* is range r1 overlapping r2 *)
let range_inter sigord_tot r1 r2 =
  List.for_all2 (fun s1 s2 -> sort_inter sigord_tot s1 s2) r1 r2

(*  *)
let ranges_are_disjoint sigord_tot r1 r2 =
  List.exists2 (fun s1 s2 -> sorts_are_disjoint sigord_tot s1 s2) r1 r2


  
(* profile consisting in a single sort *)
let sort_prof name= Union.singleton [name]

(* profile of an integer 
let int_prof= sort_prof int *)

(* bt of type BoundType.t*)
let bt_to_prof bt=
		let elt_list= List.map (fun (l,_)-> 
					(List.map 
						(fun x->Names.make (base_to_string x))
						l))
					(BoundType.elements bt) in
		Union.of_list elt_list


(* parition of unions, for grouping by arities *)
module ArUnion=Set.Make(struct type t=Union.t let compare=Union.compare end)

(* turn a profile into a set of nonempty sets of list, grouped by arity *)
let group_arities prof=
	(* pick one arity from remain and put it in acc_sets *)
	let rec extract acc_sets remain=
		if Union.is_empty remain then acc_sets else
		let k=List.length (Union.choose remain) in
		let (groupk,remain2)=Union.partition (fun ar-> List.length ar=k) remain in
		extract (ArUnion.add groupk acc_sets) remain2
	in extract ArUnion.empty prof	
	
(* tells if a profile has arity1, by picking any tuple in it (we assume no overloading) *)
let arity1 prof=
	let l=Union.choose prof in 
	List.length l=1

(*product of profiles *)
let prof_prod p1 p2 = 
  Union.fold (fun x acc -> 
	      let temp=Union.fold (fun y acc2-> Union.add (x@y) acc2) 
				  p2 Union.empty
	      in Union.union temp acc) 
	     p1 
	     Union.empty


(* intersection of signatures names *)
let bname_inter sigord b1 b2=failwith "TBD"
	
let prof_join sigord prof1 prof2 = 
  let types1 = Union.to_list prof1 in
  let types2 = Union.to_list prof2 in
  let select (type1, type2) =
    let lg_type1 = length type1 in
    match type2 with
      | s :: type2_short when (sort_inter sigord (last type1)  s) ->
          let type1_short = take (lg_type1 -1) type1  in
          Some ( type1_short @ type2_short)
      | _ -> None
  in
  let domains =
    cartesian_product types1 types2 |> filter_map select |> unique_cmp
  in Union.of_list domains

let prof_domain prof =
  let types = Union.to_list prof in
  let select l = 
    match l with 
    | s :: [s2] -> Some (s)
    | _ -> None 
  in
  filter_map select types

let prof_codomain prof =
  let types = Union.to_list prof in
  let select l = 
    match l with 
    | _ :: [s]  -> Some (s)
    | _ -> None 
  in
  filter_map select types


let mult_to_string m = match m with
  | Some `Some -> "Some"
  | Some `One -> "One"
  | Some `Lone -> "Lone"
  | None -> " "		    
  | _ -> failwith "Profile:mult_to_string: not in some_one_lone"

let print_sigmult sigmult =
  NameMap.print BatString.print (fun io mult -> BatString.print io 
                                                                (mult_to_string mult)
                                )
                stdout sigmult


(* returns a map associating each signature name with its multiplicity if it has some.
   The first parameter is of type Typing.envir_sig. 
   The second is a QNameMap containing all signatures, to add parameters not appearing in sig_list
   *)
let sigmult_from_env env sigmap =
  let open Ast_par in
  let open Typing in
  let compute_mult signame _ =
    try 
      let (_, sign)= 
	List.find (fun (qn_list,s) ->
                   List.exists (fun qn->qn_to_name qn=signame) qn_list)
                  env.sig_list
      in sign.mult
    with Not_found -> None                      
  in NameMap.mapi compute_mult sigmap


(* returns the list of the names of all the abstract signatures.
   The first parameter is of type Typing.envir_sig. 
   The second parameter is a list of (all) signature names.
 *)
let abstract_sigs_from_env env signame_list =
  let open Ast_par in
  let open Typing in
  let is_abstract signame =
    if signame = Names.univ || signame = Names.empty then false
    else
      try 
        let (_, sign)= 
	  List.find (fun (qn_list,s) ->
                     List.exists (fun qn->qn_to_name qn=signame) qn_list)
                    env.sig_list
        in sign.is_abstract
      with Not_found -> failwith ("Profile.abstract_sigs_from_env: signature " 
                                  ^ signame ^ " not found.")                    
  in
  List.filter is_abstract signame_list


(* returns the minimum number of instances that a signature must have according
   to the electrum model (the multilicity of sigs and the sigs hierarchy). 
 *)
let rec min_bound sigord sigmult abstr_sigs s =
  let open Pervasives in
  let siglist = List.of_enum (NameMap.keys (fst sigord)) in
  let min_due_to_mult =
    if mult_is_one_or_some2 sigmult s
    then
      1
    else
      0
  in
  let sons_for_extends = 
    List.filter (fun son -> is_father_for_extends sigord son s) siglist 
  in
  let sons_for_in = 
    List.filter (fun son -> is_father_for_in sigord son s) siglist 
  in
  let min1 = 
    List.fold_right (fun x y -> x+y) 
                    (List.map (min_bound sigord sigmult abstr_sigs) 
                              sons_for_extends) 
                    0 
  in
  let min2 = 
    List.fold_right max (List.map (min_bound sigord sigmult abstr_sigs) 
                                  sons_for_in) 0 
  in
  max min_due_to_mult (max min1  min2)

(* returns the maximum number of instances that a signature can have according 
   to the elctrum model (the multilicity of sigs and the sigs hierarchy). 
   returns -1 if no maximum number is forced by the model.
*)
let rec max_bound sigord sigmult abstr_sigs s =
  let open Pervasives in
  let siglist = List.of_enum (NameMap.keys (fst sigord)) in
  if mult_is_one_or_lone2 sigmult s
  then
    1
  else
    if not (List.mem s abstr_sigs)
    then
      -1
    else
      let sons_for_extends = 
        List.filter (fun son -> is_father_for_extends sigord son s) siglist 
      in
      let sons_for_in = 
        List.filter (fun son -> is_father_for_in sigord son s) siglist 
      in
      if (List.is_empty sons_for_extends) && (List.is_empty sons_for_in)
      (* if the sig is abstract and has no child 
         then it cannot have any instance *)
      then
        0
      else
        (* if the sig is abstract and has some children
           then we consider the children *)
        if (List.is_empty sons_for_extends)
             (* we consider sons for in only if there is no child for extends *)
        then
          List.fold_right (fun x y -> if x = -1 || y = -1 then -1 else  x+y)
                          (List.map (max_bound sigord sigmult abstr_sigs) 
                                    sons_for_in)
                          0 
        else
          List.fold_right (fun x y -> if x = -1 || y = -1 then -1 else  x+y)
                          (List.map (max_bound sigord sigmult abstr_sigs) 
                                    sons_for_extends)
                          0                  

