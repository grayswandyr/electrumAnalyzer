(*****************************************************************************
 * Time-stamp: <2015-10-29 CET 10:11:24 David Chemouil>
 *
 * Electrum Analyzer 
 * Copyright (C) 2014-2015 Onera; (C) 2015 IRIT
 * Authors: 
 *   Denis Kuperberg 
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
   bound_type.ml -- defines the bound type of Electrum expressions
 ****************************************************************************)

open Batteries
open Faulty
open Faulty.Infix
open Faulty.Monad

type basetype= Base_INT | Base_UNIV | Base_Sig of Ast_qname.t | Base_Ndef of Ast_qname.t

(*
   let Base_INT=Ast_qname.make false [] (Ast_ident.make "Int") (* Name of the special base type *)
   let Base_UNIV=Ast_qname.make false [] (Ast_ident.make "Univ") (* Name of universal type *)
   let Base_FORM=Ast_qname.make false [] (Ast_ident.make "Form") (* Name of boolean type for evaluating formulas *)
*)

let base_to_string base=match base with 
  | Base_INT -> "Int"
  | Base_UNIV -> "univ"
  | Base_Sig s -> Ast_qname.to_string s
  | Base_Ndef n-> "Non-defined "^(Ast_qname.to_string n)

let ident_THIS=Ast_ident.make "This" (* Identifier for the default variable 'this' *)

let base_isndef base= match base with
  |Base_Ndef _ -> true
  | _ -> false

(*
   (*inclusion of base types, only treats univ for now*)
   let base_incl x y = match y with
   |Base_UNIV -> x <> Base_FORM
   |_ ->false (*to complete with user defined subtypes*)
*)

let emptyname= Ast_qname.make false [] (Ast_ident.make "")

(* the boolean indicates if its is dynamic or static: true for dynamic *)
module BoundType= Set.Make(struct type t = basetype list * bool let compare = compare end)

type bound_type= TRel of BoundType.t | TBool  | TVarndef of Ast_qname.t


let contains_ndef btset=not (BoundType.is_empty 
                               (BoundType.filter (fun (l,b)->
                                      List.exists base_isndef l
                                    ) 
                                   btset))

(* useful functions from BoundType *)
let bt_isempty= function 
  |TRel r -> BoundType.is_empty r
  |TVarndef _ -> false
  |TBool -> false

let bt_union x y =match (x,y) with 
  |(TRel a) , (TRel b)-> TRel (BoundType.union a b)
  | TVarndef n , _ -> TVarndef n
  | _ , TVarndef n-> TVarndef n
  |TBool , TBool -> TBool (* this case seems possible, like in farmer.als, maybe problematic *) 
  | _ , _ -> assert false

(* union with erasing of nondef types *)
let bt_union_def x y =match (x,y) with 
  |(TRel a) , (TRel b)-> TRel (BoundType.union a b)
  | TVarndef n , x -> x
  | x , TVarndef n-> x
  |TBool , TBool ->TBool (* this case seems possible, like in farmer.als, maybe problematic *) 
  |_, _  -> assert false

let bt_filter f bt =match bt with 
  | TRel r -> TRel (BoundType.filter f r)
  | TVarndef nd -> TVarndef nd
  | TBool -> assert false

let bt_mem l bt=match bt with
  |TRel r-> BoundType.mem l r
  |TVarndef nd -> assert false
  |TBool -> assert false



let bt_empty=TRel (BoundType.empty)

let bt_univ = TRel (BoundType.singleton ([ Base_UNIV ],false))


(*let bt_fold f bt x=match bt with
  |TRel r-> let f_bt  
  TRel (BoundType.fold f r x)
  | _ -> assert false
*)

let bt_fold_from_empty f bt=match bt with
  |TRel r-> BoundType.fold f r bt_empty
  |TVarndef nd -> TVarndef nd
  |TBool -> assert false


let bt_map f bt=match bt with
  |TRel r-> TRel (BoundType.fold (fun x acc-> BoundType.add (f x) acc) r BoundType.empty)
  |TVarndef nd -> TVarndef nd
  |TBool -> assert false 


let bt_to_string bt=match bt with 
  |TBool -> "Bool"
  |TVarndef nd -> "Unknown "^(Ast_qname.to_string nd)
  |TRel set ->
      "{"^(BoundType.fold (fun (l,b) accset->
            let suffset= if accset="" then "" else " "^accset in
            "["^
            (List.fold_left (fun acclist base->
                   let preflist=if acclist="" then "" else acclist^";" in
                   preflist^(base_to_string base)) "" l )^"]"
            ^(if b then "d" else "s")
            ^suffset) set "")^"}"



(*detects that a type contains only relations*)
let bt_isrel bt = match bt with 
  | TRel x -> not (contains_ndef x)
  | TVarndef nd -> false
  | TBool -> false

(*detects that the type is undefined because of an unknown variable*)
let bt_isvarndef bt= match bt with 
  | TRel x ->  contains_ndef x 
  | TVarndef nd -> true
  | TBool -> false

(*detects that the type represents a boolean formula*)
let bt_isform bt= bt=TBool
let type_isform x= return (bt_isform x)

(* takes a boundtype option and says if it is an integer *)
let opt_is_int btopt=match btopt with
  |Some (TRel x) -> BoundType.mem ([Base_INT],true) x 
                    || BoundType.mem ([Base_INT],false) x 
  |_ -> false

(*faulty default types*)
let typeform= return TBool
let type_varndef nd= return (TVarndef nd)
let type_empty: (bound_type, [ `ETyping ]) Faulty.faulty= return (TRel BoundType.empty)

let type_int= return (TRel (BoundType.singleton ([Base_INT],false)))

let type_univ= return (TRel (BoundType.singleton ([Base_UNIV],false)))

let type_univ_bin=return (TRel (BoundType.singleton ([Base_UNIV;Base_UNIV],false) ))

(* fold faulty BoundType: (elt -> 'a -> 'a) -> 'a -> 'a where 'a =faulty Boundtype *)
let rec fbt_fold f s acc= s >>= fun bt-> match bt with
    |TBool -> fail `ETyping (lazy  "Folding a boolean type") 
    |TVarndef nd -> return (TVarndef nd)
    |TRel r -> if bt_isempty bt then acc else
          let l=BoundType.choose r in fbt_fold f (return (TRel (BoundType.remove l r))) (f l acc)

(*let ( >>= ) x y= bind_handle  ~hand:(function `ETyping -> function msg -> Printf.eprintf "%s\n%!" msg) x y*)

let bt_update_var bt var= match bt with
  | TRel x -> TRel (BoundType.map (fun (l,_)->(l,var)) x)
  | TVarndef nd -> bt
  | TBool -> bt


(* Product of two types
   careful : prod x {} gives x for convenience reasons *)
let bt_prod bt1 bt2= 
  if bt_isempty bt2 then bt1 else
  if bt_isempty bt1 then bt2 else
    let add1 (elt,var) btacc= 
      let newbt=bt_map (fun (x,b)-> (elt@x, b||var)) bt2 in
      bt_union newbt btacc
    in bt_fold_from_empty add1 bt1


(*computes a new BoundType by applying a function to all elements of a BoundType (to be used after filtering) *)
let apply_all f bt=match bt with 
  |TBool -> assert false
  |TVarndef nd -> TVarndef nd
  |TRel r -> TRel (BoundType.fold (fun x s->BoundType.add (f x) s) r BoundType.empty)

(*let typeapply_all f bt= lift1 (apply_all f)*)


(*
   let bt_print bt=
   match bt with 
   | TRel r->
   let rec print_bl l=match l with 
   |[] -> print_newline();
   |[b] -> print_string (base_to_string b)
   |b::q -> print_string (base_to_string b);print_string ", "; print_bl q
   in BoundType.iter print_bl r
   | TBool -> print_endline "Bool"
*)

(*environment bounding variables to types *)
module QNameMap = Map.Make(struct type t = Ast_qname.t let compare = compare end)


type 'a map= 'a QNameMap.t
let emptymap= QNameMap.empty
type envir= bound_type QNameMap.t
type envirlist= (bound_type list) QNameMap.t

(* we use uniondef here in case something is defined in only one of two environments *)
let env_add name bt env=try QNameMap.modify name (fun x -> bt_union_def bt x) env
  with Not_found -> QNameMap.add name bt env


let map_add=QNameMap.add

(* a signature is mapped to the signatures bigger than itself *)
module QNameSet = Set.Make(struct type t=Ast_qname.t let compare = compare end)

type sig_order = (QNameSet.t * bool) QNameMap.t



(*from signature name to type *)
let sigtype name var=TRel (BoundType.singleton ([Base_Sig name],var))

(* add a signature: new entry if absent, union of images if present *)
(* also add the transitive closure, i.e. the images of signatures in set *)
let addsig s (set,var) map=
  (* set to add *)
  let (newset,v)=QNameSet.fold (fun x (acc,va) -> 
        (*to check if this is really correct, may need several passes *)
        let (nset,nv)=(try QNameMap.find x map with Not_found -> (QNameSet.singleton x, var)) 
        in ((QNameSet.union acc nset), nv || va)) 
        set (set,false)  in 
  try QNameMap.modify s (fun (x,b) -> (QNameSet.union newset x , v||b||var)) map
  with Not_found-> QNameMap.add s (newset,v||var) map

(*list version (for both sides) for external use *)
let addsiglist namelist extlist var  map= List.fold_left (fun acc s-> addsig s ((QNameSet.of_list extlist),var) acc) map namelist

(* enrich an environment map with a first column described by a signature name *)
let add_first_col signame env= 
  QNameMap.map
    (fun bt->
       bt_map (fun (l,b) -> (Base_Sig signame)::l,b) bt)
    env



(*union of maps, with mergings of images when appropriate *)
let sig_union map1 map2 = QNameMap.fold addsig map1 map2

(* add a prefix to all signatures of a map *)
let sig_addpref pref sign=
  (*targets *)
  let newmap=QNameMap.map 
               (fun (names,var)-> 
                  (QNameSet.map  (fun n-> Ast_qname.add_pref pref n) names), var)
               sign
  in
  (* sources *)
  QNameMap.fold 
    (fun key set acc -> QNameMap.add (Ast_qname.add_pref pref key) set acc)
    newmap QNameMap.empty




(* is a signature present in an environment ? *)
let sig_exists signame sigord= QNameMap.mem signame sigord          

let mapfind=QNameMap.find

let env_find_list= mapfind


(* give the name of a nondefined variable *)
let bt_remain bt=match bt with 
  |TBool -> assert false
  |TVarndef n-> n
  |TRel r -> let newset= (BoundType.filter (fun (l,var) ->
        List.exists 
          (fun base->match base with 
             |Base_Ndef _->true
             |_ -> false)
          l)
        r) in
      let (l,var)=try BoundType.choose newset with Not_found -> assert false
      in let rec ndfind x= (match x with
            |[] ->assert false
            |(Base_Ndef n)::q -> n
            | _::q -> ndfind q)
      in ndfind l




(* to_string functions for types and environments *)
let sigmap_to_string sigmap=
  QNameMap.fold 
    (fun key (set,var) acc-> 
       (Ast_qname.to_string key)^": "^
       (QNameSet.fold (fun x accset-> 
              (Ast_qname.to_string x)^" "^accset) 
           set "")
       ^(if var then "v" else "s")^"\n"^acc)
    sigmap ""



let envir_to_string env=
  QNameMap.fold 
    (fun key bt acc-> 
       (Ast_qname.to_string key)^": "^
       (bt_to_string bt)^"\n"^acc)
    env ""


let envirlist_to_string env=
  QNameMap.fold 
    (fun key btlist acc-> 
       (Ast_qname.to_string key)^": "^
       (List.fold_left 
          (fun acclist bt -> if acclist="" then bt_to_string bt
            else acclist^", "^(bt_to_string bt))
          "" btlist )
       ^"\n"^acc)
    env ""



(* add a prefix to a boundtype except for a list of parameters *)
let bt_addpref_except bt pref params= match bt with
  |TBool -> TBool
  |TVarndef n-> TVarndef n
  |TRel r -> TRel (BoundType.map (fun (l,b) ->
        let l'=List.map (fun x ->
              match x with 
                |Base_INT -> Base_INT
                |Base_UNIV -> Base_UNIV
                |Base_Sig n  -> if List.mem n params then Base_Sig n else 
                      Base_Sig (Ast_qname.add_pref pref n)
                |Base_Ndef n-> Base_Ndef n)
              l in (l',b)
      ) r)


let btlist_addpref_except btl pref params= 
  List.map (fun bt->bt_addpref_except bt pref params) btl


let envir_union env1 env2 = QNameMap.fold (fun name bt acc-> env_add name bt acc) env2 env1

(* erase the background if already defined *)
let envir_union_back env envback = 
  QNameMap.fold 
    (fun name bt acc-> 
       if QNameMap.mem name acc
       then acc
       else env_add name bt acc)
    envback env

(*intersection of base types is nonempty *)
let base_inter sigord x y = 
  if x=y then true else match (x,y) with
    | (Base_UNIV, _) -> true
    | (_, Base_UNIV) ->true
    | (_ , Base_Ndef _) ->true (*we want to propagate the Ndef *)
    | (Base_Ndef _, _) -> true
    | (Base_Sig s, Base_Sig t) -> 
        (* there is a smaller sig i containing both *)
        QNameMap.exists (fun i (big,b) -> 
              (s=i || QNameSet.mem s big)
              && (t=i || QNameSet.mem t big)) sigord
        (* or both are contained in the same i *)
        ||
        ( try 
            (let (bigs,_)= QNameMap.find s sigord in
             let (bigt,_)=  QNameMap.find t sigord in
             QNameMap.exists (fun i (big,b) -> 
                   (s=i || QNameSet.mem i bigs)
                   && (t=i || QNameSet.mem i bigt)) sigord
            ) with Not_found-> failwith ("base_inter:Signature not in sigord"))
    | _, _ -> false


(*intersection of base types when nonempty *)
let base_inter_type sigord x y = 
  if x=y then x else match (x,y) with
    | (Base_UNIV, _) -> y
    | (_, Base_UNIV) ->x
    | (Base_INT, Base_INT) ->Base_INT
    | (_ , Base_Ndef n) -> Base_Ndef n (*we want to propagate the Ndef *)
    | (Base_Ndef n, _) -> Base_Ndef n
    | (Base_INT, _) -> failwith "base_inter_type with int, rel"
    | (_, Base_INT) -> failwith "base_inter_type with rel, int"
    | (Base_Sig s, Base_Sig t) -> try 
          let (a,b) = QNameMap.choose 
                        (QNameMap.filter (fun i (big,b) -> (s=i || QNameSet.mem s big)
                                                           && (t=i || QNameSet.mem t big)) sigord)
          in Base_Sig a
        with Not_found -> 
          let (bigs,_)= QNameMap.find s sigord in
          let (bigt,_)=  QNameMap.find t sigord in
          try
            let (a,b) = QNameMap.choose  
                          (QNameMap.filter (fun i (big,b) -> 
                                 (s=i || QNameSet.mem i bigs)
                                 && (t=i || QNameSet.mem i bigt)) sigord)
            in Base_Sig a
          with Not_found ->
            failwith "base_inter_type unknown intersection"

(* returns the intersection type *)
let bt_inter sigord bt1 bt2= 
  verify_arg 
    ((bt_isrel bt1 && bt_isrel bt2)
     || bt_isvarndef bt1 || bt_isvarndef bt2)
    "bt_inter called with boolean type";
  match (bt1,bt2) with 
    |(TRel r1, TRel r2) ->
        let bound_inter (l,var)=
          let bt2_f= bt_filter
                       (fun (y,vy)-> List.length y=List.length l && List.for_all2 (fun a b-> base_inter sigord a b) l y) bt2 
          in apply_all (fun (l2,v2) -> (List.map2 (base_inter_type sigord) l l2), v2||var) bt2_f
        in  bt_fold_from_empty (fun x s->bt_union (bound_inter x) s) bt1 
    | TVarndef nd , _ -> TVarndef nd
    | _ , TVarndef nd -> TVarndef nd
    |( _, _) -> assert false

(* inclusion of base types *)
let base_incl sigord x y= 
  match (x,y) with
    | (_, Base_UNIV) ->true
    | (_ , Base_Ndef n) -> true (* benefice of the doubt, Ndef will be passed on *)
    | (Base_Ndef n, _) -> true
    | (Base_UNIV, _) -> false
    | (Base_INT, Base_INT) -> true
    | (Base_INT, _) -> false
    | (_, Base_INT) -> false
    | (Base_Sig s, Base_Sig t) -> 
        let (set,b)= try (QNameMap.find s sigord)
          with Not_found -> assert false
        in s=t || QNameSet.mem t set


(* type inclusion, on relational types *)
let bt_incl sigord bt1 bt2=
  verify_arg 
    ((bt_isrel bt1 && bt_isrel bt2)
     || bt_isvarndef bt1 || bt_isvarndef bt2)
    "bt_incl called with boolean type";
  match (bt1,bt2) with
    |(TRel r1, TRel r2) ->
        (* one inclusion in bt2*)
        let one_incl (l1,b1)=
          BoundType.exists 
            (fun (l2,b2) -> try List.for_all2 (base_incl sigord) l1 l2
              with Invalid_argument _ -> false)
            r2
        in  BoundType.for_all (one_incl) r1
    | TVarndef nd , _ -> true (*benefice of the doubt, Ndef is passed on *)
    | _ , TVarndef nd -> true
    | _ , _ -> assert false



(*Join of two bounded types, using intersecting single sorts as joints*)  (*to simplify, maybe no need for internal faulty types*)
let bt_join sigord bt1_f bt2_f= bt1_f >>= fun bt1 -> bt2_f >>= fun bt2 ->
  match (bt1,bt2) with 
    |(TRel r1, TRel r2) ->
        let rec join_one curset (elt,var) accset= 
          curset >>= fun xcur -> if (BoundType.is_empty xcur || List.is_empty elt) then accset else
            match BoundType.choose xcur with
              |[],_ ->fail `ETyping (lazy  "Empty type in join")
              |(s1::q1),b ->
                  (match List.rev elt with
                    |[] -> assert false
                    |(s2::q2) -> 
                        let newset=if base_inter sigord s1 s2 then
                            accset >>= fun x-> return (BoundType.add ((List.rev q2)@q1,b||var) x) 
                          else accset
                        in let newcur=return (BoundType.remove (s1::q1,b) xcur)
                        in join_one newcur (elt,var) newset)
        in
        let join2 x acc = acc>>= fun a-> (match a with
              |TRel ra -> join_one (return r2) x (return ra) >>= fun r -> return (TRel r)
              |TVarndef nd -> return (TVarndef nd)
              |TBool -> assert false)
        in fbt_fold join2 bt1_f type_empty 
    | TVarndef nd , _ -> return (TVarndef nd)
    | _ , TVarndef nd -> return (TVarndef nd)
    |( _, _) -> fail `ETyping (lazy  "Join of boolean type")



(*Application of first type to second : eat [A,B,C] [A,B] gives [C]*)
let bt_eat sigord bt1_f bt2_f= bt1_f >>= fun bt1 -> bt2_f >>= fun bt2 ->
  match (bt1,bt2) with 
    |(TRel f, TRel arg) ->
        (* returning [] means it cannot be applied *)
        let rec apply_one (fl,v1) (argl,v2)= 
          let b = v1||v2 in
          match (fl,argl) with
            | [], _ -> ([], b)
            | _, [] -> (fl,b)
            | t1::q1, t2::q2 -> 
                if base_inter sigord t1 t2 
                then apply_one (q1,v1) (q2,v2)
                else ([],b)
        in
        (* we now apply an argument to the whole f and gather the results *)
        let eat_one arglb=
          BoundType.fold
            (fun flb acc -> 
               match apply_one flb arglb with
                 |[],_ -> acc
                 | x  -> BoundType.add x acc)
            f BoundType.empty
        in let res=BoundType.fold 
                     (fun arglb accres -> BoundType.union accres (eat_one arglb))
                     arg BoundType.empty 
        in 
        if BoundType.is_empty res
        then 
          let err_string=
            "Function application returns empty type:"^
            (bt_to_string bt1)^" to "^(bt_to_string bt2)
          in fail `ETyping (lazy err_string)
        else return (TRel res)
    | TVarndef nd , _ -> return (TVarndef nd)
    | _ , TVarndef nd -> return (TVarndef nd)
    |( _, _) -> fail `ETyping (lazy  "Eat of boolean type")
(*Join of two bounded types, using intersecting single sorts as joints
  we assume the join is ok, and do not treat faulty types *)

let bt_join_ok sigord bt1 bt2=
  match (bt1,bt2) with 
    |(TRel r1, TRel r2) ->
        let rec join_one curset (elt,var) accset= 
          if (BoundType.is_empty curset || List.is_empty elt) then accset else
            match BoundType.choose curset with
              |[],_ ->failwith "Empty type in join_ok"
              |(s1::q1),b ->
                  (match List.rev elt with
                    |[] -> assert false
                    |(s2::q2) -> 
                        let newset=if base_inter sigord s1 s2 then
                            BoundType.add ((List.rev q2)@q1,b||var) accset
                          else accset
                        in let newcur=BoundType.remove (s1::q1,b) curset
                        in join_one newcur (elt,var) newset)
        in
        let join2 x acc = (match acc with
              |TRel ra -> let r=join_one r2 x ra in (TRel r)
              |TVarndef nd -> failwith "Undefined join_ok"
              |TBool -> assert false)
        in bt_fold_from_empty join2 bt1
    | _ -> failwith "Undefined join in join_ok"


(* transitive closure: join with itself until stabilization *)
(* must be called on a relational type *)
let bt_hat sigord bt=
  if bt_isvarndef bt then bt else
    let card= match bt with
      |TRel r-> BoundType.cardinal r
      | _ -> assert false
    in 
    let rec iterate btacc n=
      if n=1 then btacc
      else iterate (bt_join_ok sigord btacc btacc) (n/2) 
    in iterate bt card



(* test if a bound type is dynamic 
   we are large, i.e. if one bool is at true in the bound type we say true
   to be improved in the future for overloading
*)
let isvar bt= match bt with
  |TRel r -> BoundType.exists (fun (l,b) -> b) r
  | _ -> false


(* add a possible flag "variable" to a bt *)
let bt_addvar bt isvar=
  if isvar=false then bt else
    match bt with 
      |TRel r ->  TRel (BoundType.map (fun (l,b) -> (l,true)) r)
      |TVarndef nd -> bt
      |_ -> failwith "Only a relation can be variable"


(* test if a bound type is mixed, i.e. relation with different arities *)
let bt_ismixed bt=match bt with
  |TRel r -> 
      let n=List.length @@ fst (BoundType.choose r) in
      BoundType.exists (fun (l,_) -> List.length l <> n) r
  |TVarndef nd -> false
  |TBool -> false
