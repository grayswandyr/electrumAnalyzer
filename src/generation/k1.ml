(*******************************************************************************
 * Time-stamp: <2015-10-29 CET 09:40:08 David Chemouil>
 * 
 * Electrum Analyzer 
 * Copyright (C) 2014-2015 Onera, (C) 2015 IRIT
 * Authors: 
 *   Denis Kuperberg 
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
open Util
open Names
open Types
open Profile

(* These are defined in Profile 

(* partial order on signatures *)
module NameMap = Map.Make(struct type t=name let compare = compare end)

(* a signature is mapped to the signatures bigger than itself *)
module NameSet = Set.Make(struct type t=name let compare = compare end)

(* equivalence classes of signatures *)
module EqClasses= Set.Make(struct type t=NameSet.t let compare = NameSet.compare end)

(* the second component gives the Equivalence classes of disjoint signatures (brothers in extends) *)
type signame_order = ((NameSet.t * bool) NameMap.t) * EqClasses.t

(*changes the qnames in names in the signature 
*)

let base_toname base= match base with
	| Base_INT -> int
	| Base_UNIV -> univ
	| Base_Sig qname -> qn_to_name qname
	| Base_Ndef qname -> failwith "Undefined signature"

let sigord_toname sigord=
	QNameMap.fold 
	(fun base (set,b) accmap -> (* b is the boolean for 'dynamic' *)
		let nbase = qn_to_name base in
		let nset = QNameSet.fold 
			(fun x acc-> NameSet.add (qn_to_name x) acc)
			set NameSet.empty
		in
		NameMap.add nbase (nset,b) accmap)
	 sigord NameMap.empty

(* is s included in t ?*)
let sort_incl sigord s t=
		let (set,b)= try (NameMap.find s sigord)
		with Not_found -> assert false
		in s=t || NameSet.mem t set


(* are two sort intersecting ? *)
let sort_inter sigord_tot s t =
	let (sigord, classes) = sigord_tot in 
	let incl=
	  if s=t then true 
	  else
		NameMap.exists (fun i (big,b) -> 
			(s=i || NameSet.mem s big)
			&& (t=i || NameSet.mem t big))
			sigord
	in let disj=
	 (* do they have parents of the same class ? *)
	 EqClasses.exists 
		(fun set -> 
		(* exists x,y in set, so disjoint *)
			NameSet.exists (fun x->
			NameSet.exists (fun y->
				(* s in x and t in y *)
				sort_incl sigord s x && sort_incl sigord t y
			) set
			) set
		) classes
	in incl && not disj

let sort_inter_type sigord_tot s t = failwith "TBD"
*)


(*
module Rel : sig
  type rel = private { 
    rel_name : name; 
    rel_prof : Profile.t
  }
  val make : name -> Profile.t -> rel
end
= struct
  type rel = { 
    rel_name : name; 
    rel_prof : Profile.t
  }
  let make rel_name rel_prof =
    { rel_name; rel_prof }
end
include Rel
*)


type un_op =
  | Trans
  | Prime
  | Tilde

type bin_op =
  | Union 
  | Inter
  | Diff 
  | Product 
  | Join

type term = {
  term : raw_term;
  profile : Profile.t
}

and raw_term =
  | TConstRel of name
  | TVarRel of name
  | TSort of name 
  | TVar of name
  | TUnop of un_op * term
  | TBinop of bin_op * term * term 
  | TIfThenElse of prop * term * term
  | TCompr of (name * term) list * prop

and int_op =
  | Add 
  | Sub 

and iexpr =
  | IConst of int 
  | IVar of name 
  | IOp of int_op * iexpr * iexpr 
  | IMult of int * iexpr 
  | ICard of term

and comp_int =
  | Lte 
  | Lt 
  | Gte 
  | Gt 
  | Eq 
  | Neq

and prop =
  (* building propositions *)
  | Equal of term * term 
  | In of term * term 
  | Comp of comp_int * iexpr * iexpr  
  (* propositional connectives *)
  | True
  | False
  | Not of prop 
  | And of prop * prop 
  | Or of prop * prop
  | Impl of prop * prop
  | Iff of prop * prop
  (* temporal connectives of future *)
  | Next of prop 
  | Always of prop 
  | Eventually of prop 
  | Until of prop * prop 
  | Release of prop * prop
  (* temporal connectives of past *)
  | Previous of prop
  | Hist of prop
  | Once of prop
  | Since of prop * prop
  (* quantifiers *)
  (* The name list is in fact expected to be a single name. *)
  (* Appears in this definition for historical reasons. *)			
  | Forall of name list * term * prop 
  | Exists of name list * term * prop 


(* Set of K1 terms, useful to handle the transitive closure in the translation K1 to K2 *)
module TermSet = Set.Make(struct type t=term let compare = Pervasives.compare end)



(* substitution of variables in a term and a prop *)
let remove_from_env env to_remove =
  let open List in
  filter (fun (x, _) -> not @@ mem x to_remove) env
    
let rec subst_prop env p =
  match p with
    | Equal (t1, t2) -> Equal (subst_term env t1, subst_term env t2)
    | In (t1, t2) -> In (subst_term env t1, subst_term env t2)
    | Comp (op, ie1, ie2) -> 
        failwith "K1.subst_prop(Comp): integers not implemented yet"
    | True -> True
    | False -> False
    | Not p -> Not (subst_prop env p)
    | And (p1, p2) -> And (subst_prop env p1, subst_prop env p2)
    | Or (p1, p2) -> Or (subst_prop env p1, subst_prop env p2)
    | Impl (p1, p2) -> Impl (subst_prop env p1, subst_prop env p2)
    | Iff (p1, p2) -> Iff (subst_prop env p1, subst_prop env p2)

    | Next p -> Next (subst_prop env p)
    | Always p -> Always (subst_prop env p)
    | Eventually p -> Eventually (subst_prop env p)
    | Until (p1, p2) -> Until (subst_prop env p1, subst_prop env p2)
    | Release (p1, p2) -> Release (subst_prop env p1, subst_prop env p2)
    | Previous p -> Previous (subst_prop env p)
    | Hist p -> Hist (subst_prop env p)
    | Once p -> Once (subst_prop env p)
    | Since (p1, p2) -> Since (subst_prop env p1, subst_prop env p2)

    | Exists (xs, t, p) ->
        let p2 = subst_prop (remove_from_env env xs) p in
        let t2 = subst_term env t in
        Exists (xs, t2, p2)
    | Forall (xs, t, p) ->
        let p2 = subst_prop (remove_from_env env xs) p in
        let t2 = subst_term env t in
        Forall (xs, t2, p2)

and subst_term env t =
  let open List in
  let term = match t.term with
    | TVar y when mem_assoc y env -> assoc y env
    | TVar _
    | TSort _ 
    | TConstRel _ 
    | TVarRel _ -> t.term
    | TUnop (op, u) -> TUnop (op, subst_term env u)
    | TBinop (op, t1, t2) -> TBinop (op, subst_term env t1, subst_term env t2)
    | TIfThenElse (p, t1, t2) ->
        TIfThenElse (subst_prop env p, subst_term env t1, subst_term env t2)
    | TCompr (bindings, p) ->
        (* the variables in bindings bind in p so we must remove them 
           from the environment *)
        let to_remove = map fst bindings in
        (* to do so: keep only those that are *not* in to_remove *)
        let env2 = remove_from_env env to_remove in
        (* besides we must substitute in the ranges of the bindings *)
        TCompr (map (fun (v, t) -> (v, subst_term env2 t)) bindings, subst_prop env2 p)
  in { t with term }


(* perform on-the-fly simplifications *)
let and1 (p1,p2)=
  match p1, p2 with
  | False, _ -> False
  | _, False -> False
  | True, _ -> p2
  | _, True -> p1
  | x, y when x = y -> x
  | _, _ -> And (p1, p2)

let or1 (p1,p2)=
	if p1=True ||p2=True then True else
	if p1= False then p2
	else if p2= False then p1
	else  Or(p1,p2)

let always1 p= 
	match p with
	| True-> True
	| False -> False
	| Always q -> Always q
	| _ -> Always p

let forall1 (xl,t,p)= 
	if p=True then True 
	else
	Forall(xl,t,p)

let exists1 (xl,t,p)= 
	if p=False then False
	else
	Exists(xl,t,p)

let rec not1 = function 
	|True -> False
	|False -> True
	|Exists (l,t,p) -> forall1 (l, t, not1 p)
	|Forall (l,t,p) -> exists1 (l , t ,not1 p)
	|Not p -> p
	|p -> Not p

let impl1 (p1,p2)= 
	match p1 with
	| True -> p2
	| False -> True
	| _ -> (match p2 with 
		| True -> True
		| False -> not1 p1
		| _ -> Impl (p1,p2)
		)

let rec iff1 = function 
  | True, True
  | False, False -> True
  | True, p
  | p, True -> p
  | False, p
  | p, False -> not1 p
  | Not p1, Not p2 -> iff1 (p1, p2)
  | (p1, p2) -> Iff (p1, p2)

let make_var_term (y, s) = {
  term = TVar y;
  profile = Profile.Union.singleton [s]
}


(* converts a list of pairs (y, s) into a tuple of type term *)
let make_tuple_term ys_ss = match ys_ss with
  | [] -> assert false
  | [(y, s)] -> make_var_term (y, s)
  | hd :: tl ->
      List.fold_left (fun acc (y, s) ->
            { term = TBinop (Product, acc, make_var_term (y, s));
              profile =
                Profile.Union.(singleton (choose acc.profile @ [s]))})
        (make_var_term hd) tl
          

let id_term = {
  term = TConstRel Names.ident;
  profile = Profile.Union.singleton [ Names.univ; Names.univ ]
}

let univ_term = {
  term = TConstRel Names.univ;
  profile = Profile.Union.singleton [ Names.univ ]
}

let empty_term = {
  term = TConstRel Names.empty;
  profile = Profile.Union.singleton [ Names.univ ]
}

let sig_term name={
  term =  TSort name;
  profile= Profile.sort_prof name}

let prod_term t1 t2={
	term=TBinop(Product, t1, t2);
 profile = prof_prod t1.profile t2.profile;}

(* makes a non-empty Cartesian product of terms, just the given term if n = 1 *)
let nprod_term ts = match ts with 
  | [] -> assert false
  | [t] -> t
  | hd :: tl ->
      List.fold_left (fun acc t ->
            { term = TBinop (Product, acc, t);
              profile = prof_prod acc.profile t.profile })
        hd tl

  (* true iff the term is variable, false if it is static. *)
let rec is_term_var sigord t =
  match t.term with 
  | TConstRel _ -> false
  | TVarRel _ -> true
  | TSort s -> is_var2 sigord s 
  | TVar _ -> false
  | TUnop (op, t2) -> is_term_var sigord t2
  | TBinop (op, t1, t2) -> is_term_var sigord t1 || is_term_var sigord t2
  | TIfThenElse (p, t1,  t2) -> 
      prop_contains_var_terms sigord p || is_term_var sigord t1 || is_term_var sigord t2
  | TCompr (l , p) -> at_least_one_term_is_var sigord l

and at_least_one_term_is_var sigord l =
  match l with 
  | [] -> false
  | (_,t) :: r -> is_term_var sigord t || at_least_one_term_is_var sigord r

and prop_contains_var_terms sigord p =
  match p with
  | True | False -> false
  | Equal (t1, t2) | In (t1, t2)  -> is_term_var sigord t1 || is_term_var sigord t2
  | Comp (op, ie1, ie2) ->
     iexpr_contains_var_terms sigord ie1 || iexpr_contains_var_terms sigord ie2
  | Not p -> prop_contains_var_terms sigord p
  | And (p1, p2) | Or (p1, p2) | Impl (p1, p2)| Iff (p1, p2)  -> 
     prop_contains_var_terms sigord p1 || prop_contains_var_terms sigord p2
  | Next p1  | Always p1 | Eventually p1 -> prop_contains_var_terms sigord p1
  | Previous p1  | Hist p1 | Once p1 -> prop_contains_var_terms sigord p1
  | Until (p1, p2) | Release (p1, p2) | Since (p1, p2) -> 
      prop_contains_var_terms sigord p1 || prop_contains_var_terms sigord p2
  | Exists (xs, t, p1) | Forall (xs, t, p1) -> 
     is_term_var sigord t || prop_contains_var_terms sigord p1
    
and iexpr_contains_var_terms sigord ie =
  match ie with
  | IConst _ -> false
  | IVar _ -> false
  | IOp (io, ie1, ie2) -> 
     iexpr_contains_var_terms sigord ie1 || iexpr_contains_var_terms sigord ie2
  | IMult (i, ie) -> iexpr_contains_var_terms sigord ie
  | ICard t -> is_term_var sigord t

let rec prop_without_temporal_op p =
  match p with
  | True | False -> true
  | Equal (t1, t2) | In (t1, t2)  -> 
      term_without_temporal_op t1 && term_without_temporal_op t2
  | Comp (op, ie1, ie2) -> 
     iexpr_without_temporal_op ie1 && iexpr_without_temporal_op ie2
  | Not p -> prop_without_temporal_op p
  | And (p1, p2) | Or (p1, p2) | Impl (p1, p2)| Iff (p1, p2)  -> 
     prop_without_temporal_op p1 && prop_without_temporal_op p2
  | Next p1  | Always p1 | Eventually p1 | Previous p1 | Hist p1 | Once p1 -> false
  | Until (p1, p2) | Release (p1, p2) | Since (p1, p2) -> false
  | Exists (xs, t, p1) | Forall (xs, t, p1) -> 
     term_without_temporal_op t && prop_without_temporal_op p1
							    
and term_without_temporal_op t =
  match t.term with 
  | TConstRel _ -> true
  | TVarRel _ -> true
  | TSort _ -> true
  | TVar _ -> true
  | TUnop (Prime, t1) -> false
  | TUnop (_, t1) ->  term_without_temporal_op t1
  | TBinop (_, t1, t2) -> term_without_temporal_op t1 && term_without_temporal_op t2
  | TIfThenElse (p, t1,  t2) -> 
     term_without_temporal_op t1 && term_without_temporal_op t2 
     && prop_without_temporal_op p
  | TCompr (_ , p) -> prop_without_temporal_op p

and iexpr_without_temporal_op ie =
  match ie with
  | IConst _ -> true
  | IVar _ -> true
  | IOp (io, ie1, ie2) -> 
     iexpr_without_temporal_op ie1 && iexpr_without_temporal_op ie2
  | IMult (i, ie) -> iexpr_without_temporal_op ie
  | ICard t -> term_without_temporal_op t


(* The first parameter is of type signame_order (used to know what sorts are variable). 
   The second parameter p is a K1 proposition.
   In case p specifies an invariant, this function returns true. Otherwise, 
   it returns false. 
   We consider p corresponds to an invariant if :
   - p = Always p1 where p1 does not contain any temporal operator,
   - p does not contain any temporal operator and p only contains static terms.
 *)

let prop_is_trivial_invar sigord p =
  match p with
  | Always p1 -> prop_without_temporal_op p1
  | _ -> prop_without_temporal_op p && not (prop_contains_var_terms sigord p)

let remove_always_in_static_fact p =
 match p with 
 | Always p1 -> p1
 | _ -> p



						      
