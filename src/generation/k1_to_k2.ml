(*******************************************************************************
 * Time-stamp: <2015-10-29 CET 09:40:19 David Chemouil>
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
open Faulty
open Names
open K1
open K2
open Util
open Profile

(* environment for K2 generation from K1 *)
type gen_env = {
  typing : bool;            (* are we generating the typing formula *)
  bindings : (name * name) list; (* currently bound variables with their respective sort*)
  sigenv : sig_env   (* environment inherited from the typing phase *)
}


let fresh, reset =
  let start = (-1) in
  let count = ref start in
  let f ?(sep = "-") base =
    incr count;
    let v = Printf.sprintf "_%s%s%d" base sep !count in
    Cfg.print_debug
    @@ Printf.sprintf "K1_to_k2.fresh: new variable %s\n%!" v;
    v
  in
  let r () = count := start
  in
  (Names.make % f, r)



let variables_to_string = Util.ListX.to_string String.print

(* says whether a variable appears in the K1 term t *) 
let rec var_is_in_term t =
  match t.term with
    | TConstRel _ -> false
    | TVarRel _ -> false
    | TSort _ -> false 
    | TVar _ -> true
    | TUnop (_, t2) -> var_is_in_term t2
    | TBinop (_, t2, t3) -> var_is_in_term t2 || var_is_in_term t3
    | TIfThenElse (p, t2, t3) -> (* a first approximation,, we should detect a variable in p *)
        true
    | TCompr _ -> true




let rec tr_clos_profile sigenv prf k =
  if k = 0
  then
    (* if bounds on the signatures in the profile of t are 0, 
       then the transitive closure is empty *)
    Union.empty
  else
  if k=1 then
    prf
  else
    let profjoin = prof_join sigenv.sigord prf prf in
    let new_prof = Union.union profjoin prf in
    tr_clos_profile sigenv new_prof (max (k lsr 1) ((k +1) lsr 1))


(* creates the formula and the set of names of relations related to
   transitive closure, for an iterated conjunction or disjunction out
   of 'xs' (applying 'f' to every x) 
   f has to return a pair in prop2 * NameSet 
*)


let rec combine_with (conn : [`Or | `And]) f xs = match xs, conn with
  | [], `Or -> (False2, TermSet.empty)
  | [], `And -> (True2, TermSet.empty)
  | [x], _ -> f x
  | hd::tl, `And -> 
      let (form_hd, tcset_hd) = f hd in
      let (form, tc_set) = combine_with conn f tl in
      (and2 (form_hd, form), TermSet.union tcset_hd tc_set)
  | hd::tl, `Or -> 
      let (form_hd, tcset_hd) = f hd in
      let (form, tc_set) = combine_with conn f tl in
      (or2 (form_hd, form), TermSet.union tcset_hd tc_set)



(* computes the maximun length of a path (x1, ... xN) such that each pair (xi, xi+1) is in a relation 
   of profile prof. 
   Used to compute the number of iterations needed for the iterative square
   method during the translation of a transitive closure term. *)
let bound_length_tr_closure sigenv prof =
  let length_is_2 l = List.length l = 2 in
  (* we keep the the part of the profile corresponding to a binary relation *)
  let pro = Union.filter length_is_2 prof |> Union.to_list in

  (* we collect the domain and the codomain in two separated lists *)
  let pro_domain = List.map List.first pro in
  let pro_codomain = List.map List.last pro in

  (* naive way of bounding the length of a path in the trasitive closure:
     the sum of the bounds of all signatures appearing in the profile*)
  let list_of_cards1 =
    try
      List.map
        (fun s -> (snd (NameMap.find (primary_sig_of sigenv s) sigenv.sigbounds)))
        (List.unique_cmp (pro_domain @ pro_codomain))
    with
      | Not_found -> failwith "k1_to_k2: transitive_closure: \ 
           no bound for a signature in the profile"
  in
  let length_bound1 = List.fold_left ( + ) 0 list_of_cards1 in

  (* smarter way of counting the maximum length of a path in the transitive 
     closure (might be greater than the naive way in simple cases) *)
  let list_of_cards2 =
    Util.ListX.flat_map
      (fun s1 ->
         List.filter_map
           (fun s2 ->
              if sort_inter sigenv.sigord s1 s2
              then Some (min
                           (snd (NameMap.find (primary_sig_of sigenv s1) 
                                   sigenv.sigbounds))
                           (snd (NameMap.find (primary_sig_of sigenv s2) 
                                   sigenv.sigbounds)))
              else None
           )
           pro_domain
      )
      pro_codomain
  in
  let length_bound2 = (List.fold_left ( + ) 0 list_of_cards2) + 2 in
  (* bound on the length of a path in the transitive closure *)
  min length_bound1 length_bound2

(* returns the term ((t + t.t).(t+ t.t) + (t + t.t)) . (...) + ...  from parameter t (here acc_term).
   The parameter k is the maximum length of a path in the transitive closure of acc_term. 
*)  
let rec iter_squares gen_env acc_term k =
  match k with
    | 0 ->    (* if bounds on the signatures in the profile of t are 0,
                 then the transitive closure is empty *)
        (* failwith ("iter_square called with length 0 for term " ^ (K1_pretty.string_of_term acc_term)) *)
        empty_term
    | 1 -> acc_term
    | _ -> 
        let profjoin = prof_join gen_env.sigenv.sigord acc_term.profile acc_term.profile in
        let new_prof = Union.union profjoin acc_term.profile in

        let new_term = 
          { term = 
              TBinop (Union,
                      {term = TBinop (Join, acc_term, acc_term) ;
                       profile = prof_join gen_env.sigenv.sigord acc_term.profile acc_term.profile ;
                      }
                     , acc_term
                     ) ;
            profile = new_prof ;
          }
        in
        iter_squares gen_env new_term (max (k lsr 1) ((k +1) lsr 1))



(* returns the list of variables in prefix order of an n-ary product encoded
   with binary products (this is because we made the mistake of not representing
   products with flat lists in the first place, bummer!) *)
let rec product_as_list t =
  let open Option.Monad in
  let ( >>= ) = bind in
  let rec pal = function
    | TVar v -> return [v]
    | TBinop (Product, t1, t2) ->
        pal t1.term >>= fun t1vars ->
        pal t2.term >>= fun t2vars ->
        return (t1vars @ t2vars)
    | _ -> None
  in pal t.term



(* 'bindings' is a list (used as a stack, consistent with BatList's assoc which
   returns the leftmost binding) (variable, sort) bindings introduced by upper
   quantifications (or possibly other constructs such as comprehensions) *)
let rec translate_prop gen_env p = 
  Cfg.print_debug
  @@ Printf.sprintf "〖%s〗\t\tbindings = %s\n%!"
       (K1_pretty.string_of_prop p)
       (ListX.to_string (Tuple2.print String.print String.print) gen_env.bindings);
  match p with
    (* building propositions *)
    | Equal (t1, t2) -> translate_eq gen_env t1 t2
    | In (t1, t2) -> translate_in gen_env t1 t2
    | Comp (op, ie1, ie2) ->
        let j1, tc_set1 =translate_int gen_env ie1 in
        let j2, tc_set2 =translate_int gen_env ie2 in
        let op2=(match op with
              | Lte -> Lte2 
              | Lt -> Lt2
              | Gte -> Gte2
              | Gt -> Gt2
              | Eq ->Eq2 
              | Neq -> Neq2) 
        in
        (Comp2 (op2, j1, j2), TermSet.union tc_set1 tc_set2)
    (* propositional connectives *)
    | True -> (True2, TermSet.empty)
    | False -> (False2, TermSet.empty)
    | Not p -> 
        let (form, trclos_set) = translate_prop gen_env p in
        (not2 form, trclos_set) 
    | And (p1, p2) ->
        let (form1, trclos_set1) = translate_prop gen_env p1 in
        let (form2, trclos_set2) = translate_prop gen_env p2 in
        (and2 (form1, form2), TermSet.union trclos_set1 trclos_set2)
    | Or (p1, p2) ->
        let (form1, trclos_set1) = translate_prop gen_env p1 in
        let (form2, trclos_set2) = translate_prop gen_env p2 in
        (or2 (form1, form2), TermSet.union trclos_set1 trclos_set2)
    | Impl (p1, p2) ->
        let (form1, trclos_set1) = translate_prop gen_env p1 in
        let (form2, trclos_set2) = translate_prop gen_env p2 in
        (impl2 (form1, form2), TermSet.union trclos_set1 trclos_set2)
    | Iff (p1, p2) ->
        let (form1, trclos_set1) = translate_prop gen_env p1 in
        let (form2, trclos_set2) = translate_prop gen_env p2 in
        (iff2 (form1, form2), TermSet.union trclos_set1 trclos_set2)
    (* temporal connectives of future *)
    | Next p -> 
        let (form, trclos_set) = translate_prop gen_env p in
        (Next2 form, trclos_set)
    | Always p -> 
        let (form, trclos_set) = translate_prop gen_env p in
        (Always2 form, trclos_set)
    | Eventually p -> 
        let (form, trclos_set) = translate_prop gen_env p in
        (Eventually2 form, trclos_set)
    | Until (p1, p2) ->
        let (form1, trclos_set1) = translate_prop gen_env p1 in
        let (form2, trclos_set2) = translate_prop gen_env p2 in
        (Until2 (form1, form2), TermSet.union trclos_set1 trclos_set2)
    | Release (p1, p2) ->
        let (form1, trclos_set1) = translate_prop gen_env p1 in
        let (form2, trclos_set2) = translate_prop gen_env p2 in
        (Until2 (form1, form2), TermSet.union trclos_set1 trclos_set2)
    (* temporal connectives of past *)
    | Previous p ->
        let (form, trclos_set) = translate_prop gen_env p in
        (Previous2 form, trclos_set)
    | Hist p ->
        let (form, trclos_set) = translate_prop gen_env p in
        (Hist2 form, trclos_set)      
    | Once p ->
        let (form, trclos_set) = translate_prop gen_env p in
        (Once2 form, trclos_set)
    | Since (p1, p2) ->
        let (form1, trclos_set1) = translate_prop gen_env p1 in
        let (form2, trclos_set2) = translate_prop gen_env p2 in
        (Since2 (form1, form2), TermSet.union trclos_set1 trclos_set2)

    (* quantifiers *)
    | Exists (xs, t, p) -> translate_quantifier gen_env `Exists xs t p
    | Forall (xs, t, p) -> translate_quantifier gen_env `Forall xs t p

(* translate integer terms from K1 to K2 *)
and translate_int gen_env intk1=
  match intk1 with
    | IConst i -> (TConst i, TermSet.empty)
    | IVar x -> failwith ("No integer variable in K2: "^x)
    | IOp (op, it1, it2) ->
        let j1, tc1 = translate_int gen_env it1 in
        let j2, tc2 = translate_int gen_env it2 in
        let op2=(match op with 
              |Add -> Add2
              |Sub -> Sub2)
        in (TBin(op2, j1, j2), TermSet.union tc1 tc2)

    | IMult (i,it) -> 
        let j, tc= translate_int gen_env it in
        (TMult(i,j), tc)
    | ICard t -> (* x in prof(t)} *)
        (* build the list xs of variables according to the profile *)
        if Union.is_empty t.profile
        then 
          failwith ("k1_to_k2.translate_int: profile is empty in a \ 
                  cardinal term.")
        else
          let l = List.length @@ Union.choose t.profile in
          if Union.exists (fun r -> (List.length r <> l)) t.profile
          then
            failwith ("k1_to_k2.translate_int: profile is not coherent in a \ 
                  cardinal term.")
          else
            let rec produce_fresh_var_list n str =
              match n with
                | 0 -> []
                | _ -> fresh str :: produce_fresh_var_list (n-1) str
            in
            let xs = produce_fresh_var_list l "x_card" in
            let form, tc = is_in gen_env xs t in
            (TCard (xs, form, t.profile) , tc)

(* if t1 and t2 are (n-ary products of) variables, we just assert their equality
   pointwise (the default case may result in far more complex formulas) *)
and translate_eq gen_env t1 t2 =
  let open List in
  match product_as_list t1, product_as_list t2 with
    | Some vs1, Some vs2 when length vs1 = length vs2 ->
        begin
          Cfg.print_debug @@
          Printf.sprintf "translate_eq: product case: %s = %s\n%!"
            (variables_to_string vs1) (variables_to_string vs2);
          combine_with `And (fun (v1, v2) -> (Equal2 (v1, v2), TermSet.empty))
          @@ combine vs1 vs2
        end
    | _ ->
        begin
          Cfg.print_debug @@
          Printf.sprintf "translate_eq: general case\n%!";
          translate_prop gen_env @@ and1 (In (t1, t2), In (t2, t1))
        end

and translate_in gen_env t1 t2 = 
  Cfg.print_debug @@
  Printf.sprintf
    "translate_in %s (: %s) %s (: %s)\t\tbindings = %s\n%!"
    (K1_pretty.string_of_term t1)
    (Profile.Union.to_string t1.profile)
    (K1_pretty.string_of_term t2)
    (Profile.Union.to_string t2.profile)
    (ListX.to_string (Tuple2.print String.print String.print) gen_env.bindings);
  let open Profile in
  (* possible ranges to build the global conjunction upon *)
  let ranges =
    t1.profile
    |> Union.filter (fun r1 ->
          let lgr1 = List.length r1 in
          Union.exists (fun r2 -> List.length r2 = lgr1) t2.profile)
    |> Union.to_list in
  Cfg.print_debug @@
  Printf.sprintf "\t\t---> computed ranges: %s\n%!"
    (ListX.to_string Range.print ranges);
  let open List in
  (* are we in the case \vec{x} in t2 or the general t1 in t2? *)
  let make_conjunct = match product_as_list t1 with
    | None ->                   (* general case *)
        let make_body xs with_binding =
          let with_env = { gen_env with bindings = with_binding } in
          let (form1, tc_set1) = is_in with_env xs t1 in
          let (form2, tc_set2) = is_in with_env xs t2 in
          (impl2 (form1, form2), TermSet.union tc_set1 tc_set2)      
        in
        let make_conjunct range =
          (* create fresh variables for sorts; and also take the
             static primary signature for variable sorts (cf #467) *)
          let new_bindings =
            map (fun r -> fresh r, primary_sig_of_if_var_sig gen_env.sigenv r) range in
          (* extract the variables just created *)
          let xs = fst @@ split new_bindings in
          (* create the body and prefix it with a chain of quantifications *)
          fold_right (fun (x, s) (r, tc_set) -> (forall2 x s r, tc_set))
            new_bindings (make_body xs (new_bindings @ gen_env.bindings))
        in
        make_conjunct 
    | Some xs -> (* case \vec{x} in t2: no need to create fresh variables in t1 *)
        fun (_ : range) -> is_in gen_env xs t2
  in
  combine_with `And make_conjunct ranges



and translate_quantifier gen_env (quant : [< `Forall | `Exists]) xs t p =
  let open List in
  Cfg.print_debug @@
  Printf.sprintf "translate_quantifier %s %s %s ---> \t\tbindings = %s\n%!"
    (variables_to_string xs)
    (K1_pretty.string_of_term t)
    (K1_pretty.string_of_prop p)
    (ListX.to_string (Tuple2.print String.print String.print) gen_env.bindings);
  let lg_xs = length xs in
  verify_arg (lg_xs = 1)
    (Printf.sprintf "K1_to_k2.translate_quantifier: \
                     number of bound variables should be 1 \
                     (here variables = %s)" (variables_to_string xs));
  let x = hd xs in
  let one_range, other_ranges = Profile.Union.pop t.profile in
  let lg = length one_range in
  verify_arg (Profile.Union.for_all (fun r -> length r = lg) other_ranges)
    (Printf.sprintf "K1_to_k2.translate_quantifier: %s %s : %s | %s : \n\
                     Not all ranges have size %d \
                     (bindings = %s)"
       ((function `Forall -> "∀" | _ -> "∃") quant)
       x
       (K1_pretty.string_of_term t)
       (K1_pretty.string_of_prop p)
       lg
       (ListX.to_string (Tuple2.print String.print String.print) gen_env.bindings)
    );
  (* if lg = 1 then *)
  (*   failwith "todo" *)
  (* else *)
  let binop, quantifier, conn = match quant with
    | `Forall -> (impl2, K2.forall2, `And)
    | `Exists -> (and2, K2.exists2, `Or)
  in
  let bodify with_bindings ys t p =
    let with_env = { gen_env with bindings = with_bindings } in
    let (form_t, tc_set_t) = is_in with_env ys t in
    let (form_p, tc_set_p) = translate_prop with_env p in
    (binop (form_t, form_p), TermSet.union tc_set_t tc_set_p)
  in
  let quantify ys_ss body =
    fold_right (fun (y, s) res -> quantifier y s res) ys_ss body
  in
  let formula_for_range r =
    (* in case we have quantifications over variable signatures, take
       their primary (static) parent signature *)
    let (ys_ss, p2) =
      if lg = 1 then (* no fresh variable to create, no substitution needed *)
        ([(x, primary_sig_of_if_var_sig gen_env.sigenv @@ hd r)], p) 
      else (* create as many fresh vars as the arity then substitute *)
        let ys_ss =  map 
                       (fun s -> (fresh s, 
                                  primary_sig_of_if_var_sig gen_env.sigenv s))
                       r 
        in
        let p2 = subst_prop [ (x, (K1.make_tuple_term ys_ss).term) ] p in
        (ys_ss, p2)
    in
    let (form_body, tc_set_body) = bodify (ys_ss @ gen_env.bindings) 
                                     (map fst ys_ss) t p2 
    in
    (quantify ys_ss form_body, tc_set_body)
  in
  combine_with conn formula_for_range @@ Profile.Union.to_list t.profile


(* gives a semantics to 'xs in term' and 'xs : term'  *)
and is_in gen_env xs term =
  Cfg.print_debug
  @@ Printf.sprintf "%s is_in %s (: %s)\t\tbindings = %s\n%!"
       (variables_to_string xs)
       (K1_pretty.string_of_term term)
       (Profile.Union.to_string term.profile)
       (ListX.to_string (Tuple2.print String.print String.print) gen_env.bindings);
  (* let xs_sorts = xs |> List.map (fun x -> *)
  (*       try *)
  (*         List.assoc x gen_env.bindings *)
  (*       with *)
  (*           Not_found -> *)
  (*             failwith @@ Printf.sprintf "K1_to_k2.is_in: no binding for %s" x *)
  (*     ) in *)
  (* let nb_xs = List.length xs in *)
  (* if term.profile *)
  (*    |> Profile.Union.filter (fun r -> List.length r = nb_xs) *)
  (*    |> Profile.Union.for_all (Profile.ranges_are_disjoint sigord xs_sorts) *)
  (* then *)
  (*   begin *)
  (*     Cfg.print_debug *)
  (*     @@ Printf.sprintf "\t\t---> [is_in] ranges do not overlap: \ *)
         (*                        return ⊥\n%!"; *)
  (*     False2 *)
  (*   end *)
  (* else *)
  match term.term with
    | TConstRel rel ->
        let open Profile in
        Cfg.print_debug
        @@ Printf.sprintf "K1_to_k2.is_in: case TConstRel %s\n%!" rel;
        (* let k = List.length xs in *)
        (* verify_arg (Union.exists (fun ar -> List.length ar = k) term.profile) *)
        (*   (Printf.sprintf "K1_to_k2.is_in(TConstRel): \ *)
             (*                    no range of size %d in %s (xs = %s)" *)
        (*      k (Union.to_string term.profile) *)
        (*      (variables_to_string xs)); *)
        (const_pred2 (K2.make rel term.profile, xs), TermSet.empty)
    | TVarRel rel ->
        let open Profile in
        Cfg.print_debug
        @@ Printf.sprintf "K1_to_k2.is_in: case TVarRel %s\n%!" rel;
        (* let k = List.length xs in *)
        (* verify_arg (Union.exists (fun ar -> List.length ar = k) term.profile) *)
        (*   (Printf.sprintf "K1_to_k2.is_in(TVarRel): \ *)
             (*                    no range of size %d in %s (xs = %s)" *)
        (*      k (Union.to_string term.profile) *)
        (*      (variables_to_string xs)); *)
        (VarPred2 (K2.make rel term.profile, xs), TermSet.empty)
    | TSort s -> 
        begin 
          Cfg.print_debug
          @@ Printf.sprintf "K1_to_k2.is_in: case TSort %s (typing? %B)\n%!"
               s gen_env.typing;
          match xs with
            | [x] ->
                let return_exists () =
                  (* x is in term if there is a y it is equal to *)
                  let y = fresh s in
                  (Exists2 (y, s, Equal2 (x, y)), TermSet.empty)
                in
                (try
                   let sx = List.assoc x gen_env.bindings in
                   (* an optimization is possible if... *)
                   if sx = s    (* the sort is the same as that of x *)
                   && not gen_env.typing (* we are not in the typing predicate *)
                   && not @@ Profile.is_var gen_env.sigenv s then (* s is not variable *)
                     begin
                       Cfg.print_debug
                       @@ Printf.sprintf "K1_to_k2.is_in: case TSort: \
                                          identical, static sort for %s ---> True2\n%!" x;
                       (True2, TermSet.empty)
                     end
                   else
                     return_exists ()
                 with Not_found -> return_exists ())
            | _::_ | [] ->
                failwith (Printf.sprintf
                            "K1_to_k2.is_in(TSort): xs should consist of 1 \
                             variable exactly (here xs = %s)"
                            (variables_to_string xs))
        end
    | TVar y ->
        Cfg.print_debug
        @@ Printf.sprintf "K1_to_k2.is_in: case TVar %s\n%!" y;
        begin match xs with
          | [x] ->
              (try
                 let sx = List.assoc x gen_env.bindings in
                 let sy = List.assoc y gen_env.bindings in
                 if Profile.sort_inter gen_env.sigenv.sigord sx sy then

                   (Equal2 (x, y), TermSet.empty)
                 else
                   begin
                     Cfg.print_debug
                     @@ Printf.sprintf "K1_to_k2.is_in: case TVar: \
                                        disjoint sort (%s : %s) not in \
                                        (%s : %s) ---> False2\n%!"
                          x sx y sy;

                     (False2, TermSet.empty)
                   end
               with Not_found -> (False2, TermSet.empty))
          | _::_ | [] ->
              failwith (Printf.sprintf
                          "K1_to_k2.is_in(TVar): xs should consist of 1 \
                           variable exactly (here xs = %s, variable = %s)"
                          (variables_to_string xs)
                          y
                       )
        end
    | TUnop (Prime, t) -> 
        begin
          Cfg.print_debug
          @@ Printf.sprintf "K1_to_k2.is_in: case Prime\n%!";

          let (form, tc_set) = is_in gen_env xs t in
          (Next2 form, tc_set)
        end
    | TBinop (Union, t1, t2) ->
        let (form1, tc_set1) = is_in gen_env xs t1 in
        let (form2, tc_set2) = is_in gen_env xs t2 in
        (or2 (form1, form2), TermSet.union tc_set1 tc_set2)
    | TBinop (Diff, t1, t2) ->
        let (form1, tc_set1) = is_in gen_env xs t1 in
        let (form2, tc_set2) = is_in gen_env xs t2 in
        (and2 (form1, not2 form2), TermSet.union tc_set1 tc_set2)
    | TBinop (Product, t1, t2) -> is_in_product gen_env xs t1 t2
    | TBinop (Join, t1, t2) -> is_in_join gen_env xs t1 t2
    | TBinop (Inter, t1, t2) ->
        let (form1, tc_set1) = is_in gen_env xs t1 in
        let (form2, tc_set2) = is_in gen_env xs t2 in
        (and2 (form1, form2), TermSet.union tc_set1 tc_set2)
    | TUnop (Tilde, t) ->
        begin match xs with
          | [x; y] -> is_in gen_env [y; x] t
          | _::_ | [] ->
              failwith (Printf.sprintf
                          "K1_to_k2.is_in(Tilde): xs should consist of 2 \
                           variables exactly (here xs = %s)"
                          (variables_to_string xs))
        end
    | TIfThenElse (p, t1, t2) ->
        let (pform, ptc_set) = translate_prop gen_env p in
        let (form1, tc_set1) = is_in gen_env xs t1 in
        let (form2, tc_set2) = is_in gen_env xs t2 in
        let yes = impl2 (pform, form1) in
        let no = impl2 (not2 pform, form2) in
        (and2 (yes, no), TermSet.union ptc_set (TermSet.union tc_set1 tc_set2))                  

    | TCompr (bs, p) ->
        let lg_xs = List.length xs in
        let lg_bindings = List.length bs in
        verify_arg (lg_xs = lg_bindings)
          (Printf.sprintf
             "K1_to_k2.is_in(TCompr): xs must be of the same length as the \
              bindings (here xs = %s and bindings = %s)"
             (variables_to_string xs) (K1_pretty.string_of_bindings bs));
        (* Build vs_xs as the substitution of variables xs for bound
           variables vs of the comprehension. *)
        (* xs_ts contains a list used to compute is_in recursively below. *)
        let xs_ts, vs_xs =
          List.fold_right2 (fun x (v, t) (rem_xs_ts, rem_vs_xs) ->
                ((x, t) :: rem_xs_ts, (v, TVar x) :: rem_vs_xs)) xs bs ([], [])
        in
        (* xs_ts_subst contains pairs (x_i, t_i) plus substitutions (up to
           the index i-1) to be performed below. *)
        let xs_ts_subst =
          List.mapi (fun i (xi, ti) -> (xi, ti, List.take i vs_xs)) xs_ts in
        let (xi_ti_form, xi_ti_tcset) = 
          combine_with `And (fun (x, t, subst) ->
                is_in gen_env [x] @@ subst_term subst t) xs_ts_subst
        in
        let (p_v_x, p_v_x_tcset) = 
          translate_prop gen_env (K1.subst_prop vs_xs p)
        in
        (and2 (xi_ti_form, p_v_x), TermSet.union xi_ti_tcset p_v_x_tcset)
        |> tap (fun (k2fml, _) ->
              Cfg.print_debug
              @@ Printf.sprintf "K1_to_k2.is_in(TCompr): \
                                 generated K2 formula for comprehension: %s\n%!"
                   (K2PPrint.k2prop_to_string k2fml))

    | TUnop (Trans, t) ->
        let length_tr_clos = 
          bound_length_tr_closure gen_env.sigenv t.profile
        in
        (* Iterative square without auxiliary relations (^t= (t + t.t).(t + t.t) + (t + t.t)...) .
           To apply if a variable is present in the term t *)
        if var_is_in_term t then
          begin
            match xs with
              | [x1; x2] -> 

                  is_in gen_env xs (iter_squares gen_env t length_tr_clos)
              | _::_ | [] -> 
                  failwith (Printf.sprintf
                              "K1_to_k2.is_in(Trans): xs should consist of 2 \
                               variables exactly (here xs = %s)"
                              (variables_to_string xs))

          end
        else
          (* Iterative square with auxiliary relations *)
          let name_of_t =
            K1_pretty.simple_string_of_term t
          in
          let name_of_trclos_t = "_tr_clos_" ^ name_of_t in
          let length_tr_clos =
            bound_length_tr_closure gen_env.sigenv t.profile
          in
          let prof_tc = tr_clos_profile gen_env.sigenv t.profile length_tr_clos in
          Cfg.print_debug @@ Printf.sprintf "K1_to_k2.is_in: case Trans t\nTerm t = %s , tr closure bound: %d\n"
                               (K1_pretty.string_of_term t)
                               length_tr_clos ;

          match xs with
            | [x1; x2] ->
                let rterm =
                  if is_term_var gen_env.sigenv.sigord t then
                    TVarRel name_of_trclos_t
                  else
                    TConstRel name_of_trclos_t
                in
                let (form, tc_set) =
                  is_in gen_env xs {term = rterm; profile = prof_tc}
                in
                (form, TermSet.add t tc_set)
            | _::_ | [] ->
                failwith (Printf.sprintf
                            "K1_to_k2.is_in(Trans): xs should consist of 2 \
                             variables exactly (here xs = %s)"
                            (variables_to_string xs))

and is_in_join gen_env xs t1 t2 =
  Cfg.print_debug
  @@ Printf.sprintf "%s is_in_join %s.%s\t\tbindings = %s\n%!"
       (variables_to_string xs)
       (K1_pretty.string_of_term t1)
       (K1_pretty.string_of_term t2)
       (ListX.to_string (Tuple2.print String.print String.print) gen_env.bindings);
  Cfg.print_debug
  @@ Printf.sprintf "is_in_join profiles: %s and %s\n%!"
       (Union.to_string t1.profile)
       (Union.to_string t2.profile);
  let open List in
  let lg_xs = length xs in
  let types1 = Profile.Union.to_list t1.profile in
  let types2 = Profile.Union.to_list t2.profile in
  (* tells whether a pair of types gives rise to a nonempty join that needs to
     yield part of a corresponding formula; in which it returns the sort
     undergoing the join as well as the split of xs into a pair (ys, zs) of
     variable lists (with adequate length w.r.t. the arity of the types) *)
  let select (type1, type2) =
    let lg_type1 = length type1 in
    let last_type1 = last type1 in
    let first_type2 = List.hd type2 in
     Cfg.print_debug 
     @@ Printf.sprintf "is_in_join.select: (%s) (%s): joinable?
       %B\n%!" 
        (Profile.Range.to_string type1) 
          (Profile.Range.to_string type2) 
         (Profile.sort_inter gen_env.sigenv.sigord last_type1 first_type2) 
    ; 
    if Profile.sort_inter gen_env.sigenv.sigord last_type1 first_type2
    && lg_type1 + length type2 = lg_xs + 2 then
      let ys, zs = split_at (lg_type1 - 1) xs in
      Some
        (Profile.sort_inter_type gen_env.sigenv.sigord last_type1 first_type2,
         ys, zs)
    else
      None
  in
  (* compute the domain joins on which we will quantify *)
  Cfg.print_debug
  @@ Printf.sprintf "is_in_join: domains %s and %s" 
  (Range.list_to_string types1) 
  (Range.list_to_string types2);
  let domains =
    cartesian_product types1 types2 |> filter_map select |> unique_cmp
  in
  verify_arg (not @@ is_empty domains) @@
  Printf.sprintf
    "K1_to_k2.is_in_join: empty join of profiles: ar(%s) = %s; ar(%s) = %s for xs=%s"
    (K1_pretty.string_of_term t1)
    (Profile.Union.to_string t1.profile)
    (K1_pretty.string_of_term t2)
    (Profile.Union.to_string t2.profile)
    (variables_to_string xs);
  let make_body = match t1.term with
    | TVar u ->                
        (* special case where we have a join u.t2 where u is a variable; this is
           common for fields, local facts... *)
        fun (_, _, zs) -> is_in gen_env (u :: zs) t2
    | _ ->
        let make_body (s, ys, zs) =
          let u = fresh s in
          let s_hull = Profile.primary_sig_of_if_var_sig gen_env.sigenv s in
          (* Cfg.print_debug @@ *)
          (* Printf.sprintf "is_in_join: created fresh %s\n%!" u; *)
          let new_bindings = (u, s_hull) :: gen_env.bindings in
          let new_env = { gen_env with bindings = new_bindings } in
          let (form1, tc_set1) = is_in new_env (ys @ [u]) t1 in
          let (form2, tc_set2) = is_in new_env (u :: zs) t2  in
          (K2.exists2 u s_hull @@ and2 (form1, form2), TermSet.union tc_set1 tc_set2 )
        in
        make_body
  in
  combine_with `Or make_body domains

and is_in_product gen_env xs t1 t2 =
  Cfg.print_debug
  @@ Printf.sprintf "%s is_in_product %s %s\t\tbindings = %s\n%!"     
       (variables_to_string xs)
       (K1_pretty.string_of_term t1)
       (K1_pretty.string_of_term t2)
       (ListX.to_string (Tuple2.print String.print String.print) gen_env.bindings)  ;
  let open List in
  let lg_xs = length xs in
  let types1 = Profile.Union.to_list t1.profile in
  let types2 = Profile.Union.to_list t2.profile in
  let select (r1, r2) =
    let lg1 = List.length r1 in
    if lg1 + List.length r2 = lg_xs
    then Some lg1
    else None
  in
  let lengths =
    cartesian_product types1 types2 |> filter_map select |> unique_cmp
  in
  let make_fml lg1 =
    let ys, zs = split_at lg1 xs in
    let  (form1, tc_set1) = is_in gen_env ys t1 in
    let  (form2, tc_set2) = is_in gen_env zs t2 in
    (and2 (form1, form2), TermSet.union tc_set1 tc_set2) 
  in
  combine_with `Or make_fml lengths


(* the first two parameters are only useful to have a nice name for the new relation *)
let rec iterative_square current_iter init_str is_term_var gen_env formula term term_tr_clos k =
  Cfg.print_debug
  @@ Printf.sprintf "iterative_square iteration %d avec k = %d: \
                     \nterm: %s profile : %s\t\t\n%!"
       current_iter k
       (K1_pretty.string_of_term term)
       (Profile.Union.to_string term.profile);
  if k = 0
  then
    (* if bounds on the signatures in the profile of t are 0,
       then the transitive closure is empty *)
    K1.False
  else
  if k = 1 then
    K1.Equal (term_tr_clos, term) 
  else
  if k=2 then
    let profjoin = prof_join gen_env.sigenv.sigord term.profile term.profile in
    let new_prof = Union.union profjoin term.profile in
    let new_formula = 
      K1.Equal
        (term_tr_clos ,
         {term =
            TBinop (Union,
                    { term = TBinop (Join, term, term) ;
                      profile = profjoin ;
                    } ,
                    term
                   );
          profile = new_prof ;}
        )
    in
    and1 (formula, new_formula)
  else
    let new_relname = (fresh "#tc") ^ "_" ^ init_str 
                      ^ "_iter_" ^ (string_of_int current_iter) in
    let profjoin = prof_join gen_env.sigenv.sigord term.profile term.profile in
    let new_prof = Union.union profjoin term.profile in
    let new_term =
      { term =
          if is_term_var then
            TVarRel new_relname
          else
            TConstRel new_relname
        ;
        profile = new_prof ;
      }
    in
    let new_formula = 
      K1.Equal
        ( new_term,
          {term =
             TBinop (Union,
                     { term = TBinop (Join, term, term) ;
                       profile = profjoin ;
                     } ,
                     term
                    );
           profile = new_prof ;}
        )
    in 
    (* recursive call to iterative_square with ceil (k/2) as the bound on
       length *)
    iterative_square (current_iter + 1) init_str is_term_var gen_env
      (and1 (formula, new_formula)) 
      new_term
      term_tr_clos
      (max (k lsr 1) ((k +1) lsr 1))

(* returns a K2 formula corresponding to the computation of the transitie closure 
   of t by iterative squares *)       

let tcformula_from_term ?(typing = false) sigenv t =
  let bindings = [] in
  let gen_env = { typing; sigenv; bindings } in
  let name_of_t = K1_pretty.simple_string_of_term t in
  let name_of_trclos_t = "_tr_clos_" ^ name_of_t in
  let length_tr_clos = 
    bound_length_tr_closure sigenv t.profile
  in
  let prof_tc = tr_clos_profile sigenv t.profile length_tr_clos in
  let tc_rawterm =
    if is_term_var sigenv.sigord t then
      TVarRel name_of_trclos_t
    else
      TConstRel name_of_trclos_t
  in
  let tc_term = {term = tc_rawterm ; profile = prof_tc} in
  if is_term_var sigenv.sigord t then
    iterative_square 1 name_of_t true gen_env K1.True t tc_term length_tr_clos
  else
    iterative_square 1 name_of_t false gen_env K1.True t tc_term length_tr_clos

(* compute the K2 formula corresponding to the computation of the transitive 
   closure of all terms in ts *)
let tcformula_from_term_set ?(typing = false) sigenv ts =
  let bindings = [] in
  let gen_env = { typing; sigenv; bindings } in  
  TermSet.fold
    (fun t k2form -> and2 (fst (translate_prop gen_env (tcformula_from_term sigenv t))
                          , k2form))
    ts
    True2  

(* retruns a pair (formula, term_set) from a K1 formula p.  
   formula is the  K2 translation of p (where transitive closures are replaced 
   by a fresh relation. 
   term_set is the set of all terms in p of which the trasitive closure is called. *)
let translate_with_tc_term_set ?(typing = false) sigenv p =
  let bindings = [] in
  let gen_env = { typing; sigenv; bindings } in
  translate_prop gen_env p 

(* tranlates a K1 formula into a K2 formula that includes constraints related 
   to transitive closures. *)
let translate ?(typing = false) sigenv p =
  let bindings = [] in
  let gen_env = { typing; sigenv; bindings } in
  let (formula, tc_set) = (translate_prop gen_env p) in
  let tc_clos_formula = 
    TermSet.fold
      (fun t k2form -> and2 (fst (translate_prop gen_env 
                                    (tcformula_from_term sigenv t))
                            , k2form))
      tc_set
      True2
  in
  if TermSet.is_empty tc_set then 
    formula 
  else
    and2 (formula, tc_clos_formula)



(***************************** TESTS *****************************)


(* let test_trans () = *)
(*   print_string "TEST TRANSITIVE CLOSURE\n"; *)
(*   let prof1 =  *)
(*     Profile.Union.add ["s1"; "s1"] (Profile.Union.singleton ["s2"; "s2"])  *)
(*   in *)

(*   let prof2 = *)
(*     let open Profile.Union in *)
(*     singleton ["s2";"s2"] *)
(*   in *)

(*   let bounds = *)
(*     NameMap.add "s1" (true, 1) (NameMap.add "s2" (true, 2) NameMap.empty) *)
(*   in *)
(*   let sigorder = *)
(*     (NameMap.add "s1" (NameSet.empty, false) *)
(*        (NameMap.add "s2" (NameSet.empty, false) NameMap.empty), *)
(*      EqClasses.singleton (NameSet.add "s1" (NameSet.singleton "s2")) *)
(*     ) *)
(*   in *)
(*   let sigenv = *)
(*     { sigord = sigorder; *)
(*       sigbounds = bounds; *)
(*     } *)
(*   in *)
(*   print_endline "Borne sur la longueur de la fermeture transitive:"; *)
(*   bound_length_tr_closure sigenv prof2 *)
(*   |> string_of_int |> print_endline; *)

(*   let t1 = { *)
(*     term = TConstRel "P"; *)
(*     profile = prof1 ; *)
(*   }       *)
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
(*   print_endline "************Formule de K1************"; *)
(*   print_endline @@ K1_pretty.string_of_prop phi1; *)

(*   print_endline "************Formule de K2************"; *)
(*   let phi2 = translate sigenv phi1 in *)
(*   PPrintX.print @@ K2PPrint.document_of_prop2 phi2; *)
(*   print_endline "\n************fin formule de K2************"; *)

(* ************************************** *)  
(* let () = Cfg.debug := true *)

(*   let s1, s2 = (Names.make "s1", Names.make "s2") *)


(*   let prof1 = *)
(*     let open Profile.Union in *)
(*     singleton [s1;s1] *)
(*       in *)
(*   let prof2 = *)
(*     let open Profile.Union in *)
(*     singleton [s1;s2] *)
(*     |> add [s1;s1] *)
(*     |> add [s1;s2;s1] *)

(*   let prof3 = *)
(*     let open Profile.Union in *)
(*     singleton [s1;s1] *)
(*       in *)
(*   let x, y, z, w = (Names.make "x", Names.make "y", Names.make "z", Names.make "w") in *)

(*       let t1 = { *)
(*     term = TConstRel "P"; *)
(*     profile = prof1 *)
(*   } *)
(*       in       *)
(*   let t2 = { *)
(*     term = TConstRel "Q"; *)
(*     profile = prof2 *)
(*   } *)
(*   in *)



(* (\* (\\***************\\) *\) *)
(* let () = reset () *)

(* let p1 = *)
(*   Equal (t1, t2) *)

(* let () = *)
(*   Printf.eprintf "*** [K1]:\nP = Q\nwith P : %a\nwith Q : %a\n\n%!" *)
(*     Profile.Union.print prof1 *)
(*     Profile.Union.print prof2 *)

(* let p1' = translate sigord p1 *)


(* let () = *)
(*   Printf.eprintf "*** [generated K2]:\n"; *)
(*   PPrintX.eprint @@ K2PPrint.document_of_prop2 p1'; *)
(*   Printf.eprintf "\n\n" *)

(* (\***************\) *)
(* let () = reset () *)

(* let p1 =  *)
(*   Impl (In (t2, t1), In (t1, t2)) *)

(* let () = *)
(*   Printf.eprintf "*** [K1]:\nQ in P ⇒ P in Q\nwith P : %a\nwith Q : %a\n\n%!" *)
(*     Profile.Union.print prof1 *)
(*     Profile.Union.print prof2 *)

(* let p1' = translate sigord p1 *)


(* let () = *)
(*   Printf.eprintf "*** [generated K2]:\n"; *)
(*   PPrintX.eprint @@ K2PPrint.document_of_prop2 p1'; *)
(*   Printf.eprintf "\n\n" *)


(* (\***************\) *)
(* (\* let () = reset () *\) *)

(* (\* let t3 = { *\) *)
(* (\*   term = TBinop (Join, t1, t1); *\) *)
(* (\*   profile = prof3 *\) *)
(* (\* } *\) *)

(* (\* let p1 = *\) *)
(* (\*   In (t3, t2) *\) *)

(* (\* let () = *\) *)
(* (\*   Printf.eprintf "*** [K1]:\nP.P in: %a\nwith Q in : %a\n\n%!" *\) *)
(* (\*     Profile.Union.print prof3 *\) *)
(* (\*     Profile.Union.print prof2 *\) *)

(* (\* let p1' = translate sigord p1 *\) *)


(* (\* let () = *\) *)
(* (\*   Printf.eprintf "*** [generated K2]:\n"; *\) *)
(* (\*   PPrintX.eprint @@ K2PPrint.document_of_prop2 p1'; *\) *)
(* (\*   Printf.eprintf "\n\n" *\) *)


