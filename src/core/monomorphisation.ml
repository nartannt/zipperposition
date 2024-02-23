module T = Term
module Lit = Literal
module Ty = Type
module IT = InnerTerm
module Subst = Subst
module Sc = Scoped
module TermSet = T.Set
module TypeSet = Ty.Set
module ArgMap = Map.Make (ID)
module ClauseArgMap = Map.Make (Int)
module SubstMap = Map.Make (Int)
module PbSubstMap = Map.Make (Int)

(* Note: for ease of notation, variables, functions, comments ... abuse the terms monomorphic and polymorphic 
 * our base language supports polymorphism and formally all the types we handle are polymorphic
 * instead monomorphic should be understood as instantiated (or ground i believe) and polymorphic as not that *)

(* TODO make module *)
(* TODO refactor what we can *)
(* TODO write nice documentation and comments *)
(* TODO if no new type arguments are derived, end the iterations *)
(* TODO clean up interface with the rest of the prover*)
(* TODO tests? *)
(* TODO squash all commits and make the necessary rebase so that this can be added to the main zipperposition branch*)

type basic_bounds = { relative_bound : float; absolute_cap : int; relative_floor : int }

type all_bounds = {
   loop_count : int;
   mono_ty_args_per_fun_sym : basic_bounds;
   poly_ty_args_per_fun_sym : basic_bounds;
   mono_ty_args_per_clause : basic_bounds;
   poly_ty_args_per_clause : basic_bounds;
   old_subst_per_clause : int;
   new_subst_per_clause : int;
   subst_per_ty_var : int;
   monomorphising_subst_per_clause : int;
   new_clauses_relative_bound : float;
   ty_var_limit : int;
 }

let begin_time = ref 0.0

(* it would be really nice if a similar function was a part of the iter library*)
(* given an 'a Iter and a 'a -> bool function, splits the iter into a pair using the given function *)
let iter_split filter iter =
   Iter.fold
     (fun (acc_1, acc_2) elem ->
       if filter elem then (Iter.cons elem acc_1, acc_2) else (acc_1, Iter.cons elem acc_2))
     (Iter.empty, Iter.empty) iter

(* remove duplicates from an iter *)
let remove_duplicates iter ~eq = Iter.map List.hd (Iter.group_by ~eq iter)

(* TODO add this to Type.ml (with better name) *)
let rec ty_eq ty ty' =
   match (Ty.view ty, Ty.view ty') with
      | Fun (l, ty), Fun (l', ty') ->
         if List.length l = List.length l' then List.for_all2 ty_eq l l' && ty_eq ty ty' else false
      | Forall ty, Forall ty' -> ty_eq ty ty'
      | Var var, Var var' when Ty.is_tType (HVar.ty var) && Ty.is_tType (HVar.ty var') ->
         HVar.equal (fun _ _ -> true) var var'
      | Builtin b, Builtin b' -> b = b'
      | DB i, DB i' -> i = i'
      | App (f, l), App (f', l') ->
         if List.length l = List.length l' then
            ID.equal f f' && List.for_all2 ty_eq l l' else false
      | _ -> false

(* Iter.union needs to be provided an equality function when dealing with lists of types *)
(* note that Ty.equal is a physical equality*)
let ty_arg_eq ty_arg1 ty_arg2 =
   assert (List.length ty_arg1 = List.length ty_arg2);
   List.for_all2 ty_eq ty_arg1 ty_arg2

let lit_is_monomorphic = function
   | Literal.Equation (lt, rt, _) -> T.monomorphic lt && T.monomorphic rt
   | _ -> true

(* the given type does not contain any tType *)
let is_not_meta ty = not (Type.Seq.sub ty |> Iter.exists Type.is_tType)

(* the given type is not meta and requires no type arguments*)
let ty_well_formed ty = List.for_all is_not_meta (Ty.expected_args ty) && Ty.expected_ty_vars ty = 0

(* returns the substitution that allows matching a monomorphic type against a type *)
let match_type ~pattern ~mono_type = Unif.Ty.matching_same_scope ~pattern:pattern mono_type ~scope:0

(* returns an (ID, type list) iter that represent the function symbols and their type arguments that 
 * can be extracted from the term *)
let typed_sym term =
   (*get all applications*)
   let all_apps = Iter.filter T.is_app (T.Seq.subterms term) in
   (*get all the function symbols and types at the application level*)
   let get_typed_sym app_term =
      let hd_term = T.head_term_mono app_term in
      let _ , f = T.open_fun hd_term in
      let ty = T.ty hd_term in
         match T.head f with
            | Some id when ty_well_formed ty -> Some (id, T.ty_args f)
            | _ -> None
   in
      Iter.filter_map get_typed_sym all_apps

(* applies a substitution to a type*)
let apply_ty_subst subst ty = Subst.Ty.apply Subst.Renaming.none subst (ty, 0)

(* applies a substitution to a literal *)
let apply_subst_lit lit subst = Literal.apply_subst Subst.Renaming.none subst (lit, 0)

(* merges two maps by union of their iters*)
let merge_map_arg_iter (old_ty_args_1, new_ty_args_1) (old_ty_args_2, new_ty_args_2) =
   (Iter.union ~eq:ty_arg_eq old_ty_args_1 old_ty_args_2, Iter.union ~eq:ty_arg_eq new_ty_args_1 new_ty_args_2)

(* the union of two substitution iters*)
let iter_subst_union (*Iter.union ~eq:Subst.equal ~hash:Subst.hash*) iter_1 iter_2 =
   remove_duplicates ~eq:Subst.equal (Iter.append iter_1 iter_2)

(* given a list of polymorphic (assumed to be non-monomorphic) types and monomorphic types
 * returns the composition of the substitutions of the matchings of the poly types against the mono types
 * if the substitutions are incompatible or any of the matchings fail, None is returned *)
let type_arg_list_subst_merge type_list_poly type_list_mono =
   let combine curr_subst mono_ty poly_ty =
      match curr_subst with
         | None -> None
         | Some curr_subst -> (
            try
             let new_subst = match_type ~pattern:poly_ty ~mono_type:mono_ty in
                Some (Subst.merge new_subst curr_subst)
            with
               | Subst.InconsistentBinding _ -> None
               | Unif.Fail -> Some curr_subst)
   in
   List.fold_left2 combine (Some Subst.empty) type_list_mono type_list_poly

(* given a basic bound and the size of whatever object we are bounding
 * returns the numbers of elements to keep*)
let max_nb len bound =
   let rel_cap = int_of_float (float_of_int len *. bound.relative_bound) in
   if bound.absolute_cap = -1 then rel_cap
   else min bound.absolute_cap (max bound.relative_floor rel_cap)


(* takes a map of function symbols to monomorphic type arguments
 * takes a map of function symbols to polymorphic type arguments
 * returns a pair of iters corresponding to the substitutions generated from new polymorphic type args
 * and those from old polymorphic type args and new monomorphic type args *)
let derive_type_arg_subst mono_map poly_map =
   (*derives the substitutions from two sets (iters) of type arguments*)
   let type_arg_iter_subst mono_type_args_iter poly_type_args_iter =
      let poly_arg_map mono_type_args_iter poly_type_list =
         Iter.filter_map (type_arg_list_subst_merge poly_type_list) mono_type_args_iter
      in
         Iter.flat_map (poly_arg_map mono_type_args_iter) poly_type_args_iter
   in

   let combine fun_sym (old_poly_args, new_poly_args) (new_poly_subst, old_poly_subst) =

      let old_mono_args, new_mono_args = ArgMap.find fun_sym mono_map in
      (* substitutions derived from the new poly type args *)
      let derived_new_poly_subst =
         Iter.persistent_lazy
           (type_arg_iter_subst (remove_duplicates ~eq:ty_arg_eq (Iter.append old_mono_args new_mono_args))
              new_poly_args)
      in
      (* substitutions dervied from the old poly type args and the new mono type args*)
      let derived_old_poly_subst =
         Iter.persistent_lazy (type_arg_iter_subst new_mono_args old_poly_args) in

      let new_poly_subst_res =
         remove_duplicates ~eq:Subst.equal (Iter.append new_poly_subst derived_new_poly_subst) in
      let old_poly_subst_res =
         remove_duplicates ~eq:Subst.equal (Iter.append old_poly_subst derived_old_poly_subst) in

      ((new_poly_subst_res, old_poly_subst_res))
   in
   let new_poly_subst, old_poly_subst = ArgMap.fold combine poly_map (Iter.empty, Iter.empty) in
   iter_subst_union new_poly_subst old_poly_subst

let total_time = ref 0.0

(* truncates an iter after len elements *)
let iter_truncate len iter = Iter.take len iter


let print_all_type_args ?(erase_empty = false) fun_sym iter =
   if (not erase_empty) || Iter.length (fst iter) > 0 || Iter.length (snd iter) > 0 then (
     Printf.printf "for this function symbol: %s -- we have the following type arguments  \n(old) :\n"
       (ID.name fun_sym);
     Iter.iter
       (fun ty_args -> Printf.printf "%s\n" (String.concat "; " (List.map Ty.to_string ty_args)))
       (fst iter);
     Printf.printf "(new) :\n";
     Iter.iter
       (fun ty_args -> Printf.printf "%s\n" (String.concat "; " (List.map Ty.to_string ty_args)))
       (snd iter))

(* given a subst map, an iter of substitutions and the current iteration,
   will update the map accordingly *)
let update_susbt_map all_subst curr_map curr_iteration =
   let add_single_subst subst_map subst =
      let update_map subst = function
         | None -> Some (Iter.singleton (subst, curr_iteration))
         | Some iter -> Some (Iter.cons (subst, curr_iteration) iter)
      in
         Iter.fold
           (fun curr_map ty_var -> SubstMap.update (HVar.id ty_var) (update_map subst) curr_map)
           subst_map
           (Iter.map fst (Subst.domain subst))
   in
   Iter.fold add_single_subst curr_map all_subst

(* given a single substitution and some polymorphic type argument tuples,
 * will generate at most respectively max_new_mono and max_new_poly 
 * monomorphic and non-monomorphic type arguments by application of the substitution
 * to the given type arguments*)
let apply_ty_arg_subst_split subst poly_ty_args max_new_mono max_new_poly =
   let subst_domain = Iter.map fst (Subst.domain subst) in
   (* Subst.domain returns InnerTerm.t HVar.t, we need Ty.t HVar.t *)
   let subst_ty_domain = 
      Iter.map (fun (ty_var: InnerTerm.t HVar.t) -> 
            (HVar.make ~ty:(Ty.of_term_unsafe ty_var.ty) ty_var.id) ) subst_domain
   in
   let ty_var_eq = HVar.equal ty_eq in

   (* all type variables in a type argument tuple*)
   let ty_vars ty_args =
      remove_duplicates ~eq:ty_var_eq
        (List.fold_left
           (fun acc ty -> Iter.append (Ty.Seq.vars ty) acc)
           Iter.empty ty_args)
   in

   let poly_ty_args_vars_pair = Iter.map (fun ty_args -> (ty_args, ty_vars ty_args)) poly_ty_args in

   (* a polymorphic type argument tuple is a monomorphic candidate with regards to a given substitution
    * if that substitution instantiates all its type variables *)
   let split_apply_ty_arg_subst candidates_mono candidates_poly =
      let new_mono = Iter.map (List.map (apply_ty_subst subst)) (Iter.take max_new_mono candidates_mono) in
      let new_poly = Iter.map (List.map (apply_ty_subst subst)) (Iter.take max_new_poly candidates_poly) in
      (new_mono, new_poly)
   in

   let mono_candidates, potential_poly_candidates =
      iter_split (fun (_, ty_vars) -> Iter.subset ~eq:ty_var_eq ty_vars subst_ty_domain) poly_ty_args_vars_pair
   in
   let poly_candidates =
      (* this filters out all polymorphic type argument tuples that would no be affected by the substitution
       * ie: that have no type variable instantiated by the substitution *)
      Iter.filter
        (fun (_, ty_vars) -> Iter.exists (fun ty_var -> Iter.mem ~eq:ty_var_eq ty_var subst_ty_domain) ty_vars)
        potential_poly_candidates
   in
      split_apply_ty_arg_subst (Iter.map fst mono_candidates) (Iter.map fst poly_candidates)

(* given a mono and a poly ty arg iter as well as an iter of substitutions and respective mono and poly bounds
 * will return a new mono and a new poly type arg iter within the given bounds *)
(** would be particularly profitable if we made sure all substitutions are generating lazily (as iters allow)
 * that way keeping the entire iter of generated substitutions will have little impact on performance *)
let rec generate_ty_args all_subst poly_ty_args max_new_mono max_new_poly =
   (*Printf.printf "all_subst length: %i\n" (Iter.length all_subst);*)
   let res =
      match Iter.head all_subst with
         | None -> (Iter.empty, Iter.empty, Iter.empty)
         | _ when max_new_mono <= 0 && max_new_poly <= 0 -> (Iter.empty, Iter.empty, Iter.empty)
         | Some subst ->
            (*let new_ty_args = Iter.map (List.map (apply_ty_subst subst)) poly_ty_args in*)
            (*let new_mono_ty_args_all, new_poly_ty_args_all = split_iter new_ty_args in*)
            let new_mono_ty_args, new_poly_ty_args =
               apply_ty_arg_subst_split subst poly_ty_args max_new_mono max_new_poly
            in
            let new_mono_count = max_new_mono - Iter.length new_mono_ty_args in
            let new_poly_count = max_new_poly - Iter.length new_poly_ty_args in
            let next_mono_args, next_poly_args, used_substs =
               generate_ty_args (Iter.drop 1 all_subst) poly_ty_args new_mono_count new_poly_count
            in
               ( Iter.append new_mono_ty_args next_mono_args,
                 Iter.append new_poly_ty_args next_poly_args,
                 Iter.cons subst used_substs )
   in
      res

(* given an iter of type variables, returns true iff the substitutions are equal on the set of type variables*)
let restricted_subst_eq (ty_var_iter : Ty.t HVar.t Iter.t) subst_1 subst_2 =
   let eq_sc_term_opt t1 t2 =
      match (t1, t2) with
         | Some t1, Some t2 -> InnerTerm.equal (fst t1) (fst t2)
         | None, None -> true
         | _ -> false
   in
      Iter.for_all
        (fun ty_var -> eq_sc_term_opt (Subst.find subst_1 (ty_var, 0)) (Subst.find subst_2 (ty_var, 0)))
        (ty_var_iter :> InnerTerm.t HVar.t Iter.t)

(* computes bounds relative to function symbols *)
let max_new_ty_args fun_sym mono_map poly_map bounds =
   let all_mono_ty_args = ArgMap.find fun_sym mono_map in
   let all_poly_ty_args = ArgMap.find fun_sym poly_map in
   let max_mono_bound =
      max_nb
        (Iter.length (fst all_mono_ty_args) + Iter.length (snd all_mono_ty_args))
        bounds.mono_ty_args_per_fun_sym
   in
   let max_poly_bound =
      max_nb
        (Iter.length (fst all_poly_ty_args) + Iter.length (snd all_poly_ty_args))
        bounds.poly_ty_args_per_fun_sym
   in
      (max_mono_bound, max_poly_bound)

(* given the poly map of a clause and the mono map
 * given an iter of substitutions derived from new poly type args
 * given an iter of substitutions derived from old poly type args and new mono type args
 * returns an updated mono and poly map, where the substitutions have been applied (with respect to the bounds)
 * returns an iter of the substitutions that were actually used*)
let apply_subst_map mono_map poly_map new_subst_all bounds =
   let clause_poly_total =
      ArgMap.fold
        (fun _ (old_ty_args, new_ty_args) acc -> acc + Iter.length old_ty_args + Iter.length new_ty_args)
        poly_map 0
   in

   let mono_clause_max = max_nb clause_poly_total bounds.mono_ty_args_per_clause in
   let poly_clause_max = max_nb clause_poly_total bounds.poly_ty_args_per_clause in

   (* given a function symbol and the associated poly type arguments will update the acc_maps
    * and acc_remaining that represents the number of remaining type arguments we can generate *)
   let update_maps fun_sym (old_poly_ty_args, new_poly_ty_args) (acc_maps, acc_remaining, acc_used_subst) =
      (* we compute various bounds, we have the bounds that limit the number of new type arguments
       * that we can generate relative to the existing number of type arguments
       * we also have bounds that limit the number of new type arguments that can be generated for
       * each clause *)
      let remaining_clause_mono, remaining_clause_poly = acc_remaining in
      let remaining_fun_sym_mono, remaining_fun_sym_poly = max_new_ty_args fun_sym mono_map poly_map bounds in
      let remaining_local_mono = min remaining_clause_mono remaining_fun_sym_mono in
      let remaining_local_poly = min remaining_clause_poly remaining_fun_sym_poly in

      let acc_mono_map, acc_poly_map = acc_maps in

      (* applying substitutions derived from new poly type args to new type args *)
      let new_mono_ty_args, new_poly_ty_args, used_subst =
         generate_ty_args new_subst_all new_poly_ty_args remaining_local_mono remaining_local_poly
      in
      let remaining_local_mono = remaining_local_mono - Iter.length new_mono_ty_args in
      let remaining_local_poly = remaining_local_poly - Iter.length new_poly_ty_args in

      (* applying substitutions derived from new poly type args to old type args *)
      let new_mono_ty_args_2, new_poly_ty_args_2, used_subst_2 =
         generate_ty_args new_subst_all old_poly_ty_args remaining_local_mono remaining_local_poly
      in

      (*let remaining_local_mono = remaining_local_mono - Iter.length new_mono_ty_args_2 in
        let remaining_local_poly = remaining_local_poly - Iter.length new_poly_ty_args_2 in*)

      (* applying substitutions derived from old poly type args and new mono type args to
       * new poly type args, we don't apply these substitutions to old poly type args because
       * this has already been done in a previous iteration (modulo bound limitations) *)
      (*let new_mono_ty_args_3, new_poly_ty_args_3, used_subst_3 =
           generate_ty_args old_poly_subst_all new_poly_ty_args remaining_local_mono remaining_local_poly in

        (* TODO remove separation of new and old subst*)
        let new_mono_ty_args_4, new_poly_ty_args_4, used_subst_4 =
           generate_ty_args old_poly_subst_all old_poly_ty_args remaining_local_mono remaining_local_poly in*)

      (*let new_mono_ty_args_4, new_poly_ty_args_4, used_subst_4 = Iter.empty, Iter.empty, Iter.empty in*)

      (* TODO remove duplicates (ez)*)
      let all_new_mono_ty_args =
         remove_duplicates ~eq:ty_arg_eq (Iter.append new_mono_ty_args new_mono_ty_args_2)
      in
      (*(Iter.append new_mono_ty_args (Iter.append new_mono_ty_args_2 (Iter.append new_mono_ty_args_3 new_mono_ty_args_4))) in*)
      let all_new_poly_ty_args =
         remove_duplicates ~eq:ty_arg_eq (Iter.append new_poly_ty_args new_poly_ty_args_2)
      in

      (*Iter.append new_poly_ty_args new_poly_ty_args_2 in*)
      (*(Iter.append new_poly_ty_args (Iter.append new_poly_ty_args_2 (Iter.append new_poly_ty_args_3 new_poly_ty_args_4))) in*)

      (* we need to keep track of the substitutions used to generate the type arguments in order
         to later generate the clauses *)
      let all_used_substs =
         (*Iter.append acc_used_subst (Iter.append (Iter.append used_subst used_subst_2) (Iter.append used_subst_3 used_subst_4)) in*)
         Iter.append used_subst used_subst_2
      in

      let new_mono_map = ArgMap.add fun_sym all_new_mono_ty_args acc_mono_map in
      let new_poly_map = ArgMap.add fun_sym all_new_poly_ty_args acc_poly_map in

      let remaining_clause_mono = remaining_clause_mono - Iter.length all_new_mono_ty_args in
      let remaining_clause_poly = remaining_clause_poly - Iter.length all_new_poly_ty_args in

      ((new_mono_map, new_poly_map), (remaining_clause_mono, remaining_clause_poly), all_used_substs)
   in

   let (new_mono_map, new_poly_map), _, used_substs =
      ArgMap.fold update_maps poly_map
        ((ArgMap.empty, ArgMap.empty), (mono_clause_max, poly_clause_max), Iter.empty)
   in
      (new_mono_map, new_poly_map, used_substs)

(* takes a map from functions symbols to sets (iter for now) of monomorphic type arguments
 * takes an array of literals
 * takes a map from clause_ids to a map of function symbols to sets (iter for now) of monomorphic type arguments
 * takes a map from clause_ids to a map of type variables to iters of (substitution, int) pairs
 * this stores all the generated substitutions for each type variable, the integer is used to keep track of the
 * iteration at which it was generated
 * returns a map of new monomorphic type arguments
 * returns a map of new polymorphic type arguments
 * returns the updated substitution map *)
let mono_step_clause mono_type_args_map poly_type_args_map susbt_clause_map curr_iteration literals bounds =
   if false then (
     Printf.printf "Monomorphic\n";
     ArgMap.iter (fun fun_sym iter -> print_all_type_args fun_sym iter ~erase_empty:true) mono_type_args_map;
     Printf.printf "Polymorphic\n";
     ArgMap.iter (fun fun_sym iter -> print_all_type_args fun_sym iter ~erase_empty:true) poly_type_args_map);

   (*generate all substitutions from mono and poly type arguments*)
   let new_subst_all = derive_type_arg_subst mono_type_args_map poly_type_args_map in

   (*Printf.printf "new substitutions: %i\n" (Iter.length new_poly_subst_all + Iter.length old_poly_subst_all);*)

   (*apply the substitutions to the poly type arguments*)
   (*split them into the new_mono and new_poly type arguments*)
   let new_mono_map_all, new_poly_map_all, used_substs_iter =
      apply_subst_map mono_type_args_map poly_type_args_map new_subst_all bounds
   in

   (new_mono_map_all, new_poly_map_all, update_susbt_map used_substs_iter susbt_clause_map curr_iteration)

(* takes a map from function symbols to sets (iter for now) of monomorphic type arguments
 * takes a map from clause_ids to a map from function symbols to sets (iter for now) of polymorphic type arguments
 * takes a list of clauses under the form of a (clause_id * literal array) (clause_ids are ints)
 * returns an updated monomorphic map, polymorphic map and list of updated clauses *)
let mono_step clause_list mono_map poly_clause_map subst_map curr_iter bounds =
   (*Printf.printf "We have %i total literals\n" !all_arr_len;*)

   (* given an accumulator that contains a list of clauses and two type argument maps (one mono and one poly)
    * returns an accumulator updated with regards to the given literals*)
   let process_clause acc (clause_id, literals) =
      let acc_subst, acc_mono_map, acc_poly_clause_map = acc in

      (*assuming it doesn't fail because we previously add all clause ids to the poly_clause_map*)
      let poly_map = ClauseArgMap.find clause_id poly_clause_map in

      let old_clause_subst_map = PbSubstMap.find clause_id subst_map in

      let new_mono_map, new_poly_map, new_clause_subst_map =
         mono_step_clause mono_map poly_map old_clause_subst_map curr_iter literals bounds
      in

      let merge_iter _ iter_1 iter_2 = Some (remove_duplicates ~eq:ty_arg_eq (Iter.append iter_1 iter_2)) in
      let res_mono_map = ArgMap.union merge_iter new_mono_map acc_mono_map in
      (* this entails that if two clauses have the same id, then the type arguments derived from the earlier
       * ones will be overwritten*)
      let res_poly_clause_map = ClauseArgMap.add clause_id new_poly_map acc_poly_clause_map in

      (*let new_clause_list = Iter.to_list (Iter.map (fun lit_arr -> clause_id, lit_arr) new_mono_clauses) in*)
      let res_subst_map = PbSubstMap.add clause_id new_clause_subst_map acc_subst in

      (res_subst_map, res_mono_map, res_poly_clause_map)
   in
   let new_subst_map, new_mono_map_all, new_poly_clause_map =
      List.fold_left process_clause (subst_map, ArgMap.empty, ClauseArgMap.empty) clause_list
   in
   (*Printf.printf "we have %i substitutions\n" subst_count;*)
   let new_mono_map = new_mono_map_all in
   let age_map original_map extra_map =
      let new_args_iter fun_sym =
         match ArgMap.find_opt fun_sym extra_map with Some iter -> iter | None -> Iter.empty
      in
      let iter_age_mapi fun_sym (old_iter, new_iter) =
         (Iter.union ~eq:ty_arg_eq old_iter new_iter, new_args_iter fun_sym)
      in
         ArgMap.mapi iter_age_mapi original_map
   in
   let res_mono_map = age_map mono_map new_mono_map in
   let clause_map_age clause_id original_poly_map =
      match ClauseArgMap.find_opt clause_id new_poly_clause_map with
         | None -> age_map original_poly_map ArgMap.empty
         | Some extra_poly_map -> age_map original_poly_map extra_poly_map
   in
   let res_poly_clause_map = ClauseArgMap.mapi clause_map_age poly_clause_map in
      (new_subst_map, res_mono_map, res_poly_clause_map)

(* takes a map from function symbols to sets (iter for now) of monomorphic type arguments
 * same for polymorphic type arguments
 * takes a term
 * returns the maps updated with the additional function symbol -> type arguments bindings derived from the term
 * note that all function symbols are added to the maps, even when no corresponding type arguments are found
 * this is to avoid trouble when ArgMap.find is used later *)
(* we assume this function is used only for the initialisation of the maps and that they contain no new type
 * arguments *)
let add_typed_sym mono_map poly_map term =
   let typed_symbols = typed_sym term in
   let type_args_are_mono = List.for_all Ty.is_ground in
   let map_update_fun ty_args add_args = function
      | None when add_args -> Some (Iter.empty, Iter.singleton ty_args)
      | Some (_, curr_iter) when add_args -> Some (Iter.empty, Iter.cons ty_args curr_iter)
      | None -> Some (Iter.empty, Iter.empty)
      | Some (_, curr_iter) -> Some (Iter.empty, curr_iter)
   in
   (*using tuples because this function will be used in a fold*)
   let update_maps (curr_mono_map, curr_poly_map) (ty_sym, ty_args) =
      (* this removes function symbols with no type arguments (ex: nat, bool, ...) *)
      if false then (curr_mono_map, curr_poly_map)
      else
        let ty_args_mono = type_args_are_mono ty_args in
        let new_mono_map = ArgMap.update ty_sym (map_update_fun ty_args ty_args_mono) curr_mono_map in
        let new_poly_map = ArgMap.update ty_sym (map_update_fun ty_args (not ty_args_mono)) curr_poly_map in
           (new_mono_map, new_poly_map)
   in
   let res_mono_map, res_poly_map = Iter.fold update_maps (mono_map, poly_map) typed_symbols in

   (* makes sure all function symbols have been added to the mono_map, to be later removed when find_opt
    * replaces find *)
   (*(assert (Iter.for_all (fun (fun_sym, _) -> ArgMap.find_opt fun_sym res_mono_map != None) typed_symbols));
     (assert (Iter.for_all (fun (fun_sym, _) -> ArgMap.find_opt fun_sym res_poly_map != None) typed_symbols));
     (assert (ArgMap.for_all (fun fun_sym _ -> ArgMap.find_opt fun_sym res_mono_map != None) res_poly_map));*)
   (res_mono_map, res_poly_map)

(* for a clause, removes polymorphic type arguments that contain one or more type variables which cannot be instantiated *)
(* the test is making sure that the mono_map is empty for every function symbol in which the type variable appears, so some
 * type variables which can't be instantiated will not be removed *)
(* the likelihood of a type argument being instantiated decreases with each type variable, hence the ty_var_limit
 * for polymorphic type arguments (for now it is set to 2, which is based off of the fact it feels like a good number) *)
let poly_ty_args_filter mono_map poly_map ty_var_limit =
   let ty_var_eq = HVar.equal ty_eq in
   let vars_of_ty_arg ty_list =
      remove_duplicates ~eq:ty_var_eq
        (List.fold_left (fun acc ty -> Iter.union ~eq:ty_var_eq acc (Ty.Seq.vars ty)) Iter.empty ty_list)
   in
   let ty_args_filter ty_list =
      let ty_args_ty_vars = vars_of_ty_arg ty_list in
         Iter.length ty_args_ty_vars <= ty_var_limit
   in
   let ty_arg_map_map (_, ty_args_iter) =
      ( Iter.empty,
        remove_duplicates ~eq:ty_arg_eq (Iter.persistent_lazy (Iter.filter ty_args_filter ty_args_iter)) )
   in
      ArgMap.map ty_arg_map_map poly_map

(* given an array of literals, returns an iter of all the terms in literals *)
let terms_iter literals = Literals.Seq.terms literals

let init_single_subst_map literals =
   let all_vars = Literals.Seq.vars literals in
   let all_ty_vars = Iter.filter (fun var -> Type.equal (HVar.ty var) Type.tType) all_vars in
      Iter.fold (fun acc ty_var -> SubstMap.add (HVar.id ty_var) Iter.empty acc) SubstMap.empty all_ty_vars

(* will initialise the maps with the function symbol -> type arguments bindings derived from the clauses *)
let map_initialisation_step (mono_map, clause_poly_map, pb_subst_map) (clause_id, literals) =
   (* TODO find out precisely whether this persistent is useful *)
   let clause_terms_iter = Iter.persistent_lazy (terms_iter literals) in

   let update_maps (curr_mono_map, curr_poly_map) term = add_typed_sym curr_mono_map curr_poly_map term in
   let new_subst_map = PbSubstMap.add clause_id (init_single_subst_map literals) pb_subst_map in
   let new_mono_map, new_poly_map = Iter.fold update_maps (mono_map, ArgMap.empty) clause_terms_iter in

   let remove_duplicate_init map =
      (* we can ignore the first item because it will be empty*)
      (* TODO in fact it would be better to generate a single iter and slot it into a tuple now *)
      ArgMap.map (fun (_, iter) -> (Iter.empty, remove_duplicates ~eq:ty_arg_eq (Iter.persistent iter))) map
   in
   let new_poly_map_unique = remove_duplicate_init new_poly_map in
   let new_clause_poly_map =
      match ClauseArgMap.find_opt clause_id clause_poly_map with
         | None -> ClauseArgMap.add clause_id new_poly_map_unique clause_poly_map
         (*should not happen if each clause has a unique id*)
         | Some other_poly_map ->
            Printf.printf "Warning: different clauses have the same id\n";
            ClauseArgMap.add clause_id
              (ArgMap.union
                 (fun _ pair_1 pair_2 -> Some (merge_map_arg_iter pair_1 pair_2))
                 new_poly_map_unique other_poly_map)
              clause_poly_map
   in

   (* The assert represent invariants which hold true, checking them is not necessary *)
   (*let all_ty_syms = Iter.flat_map typed_sym clause_terms_iter in

     (assert (ArgMap.for_all (fun fun_sym _ -> ArgMap.find_opt fun_sym new_mono_map != None) new_poly_map));
     (assert (Iter.for_all (fun (fun_sym, _) -> ArgMap.find_opt fun_sym new_mono_map != None) all_ty_syms));
     (assert (ClauseArgMap.for_all (fun _ poly_map -> ArgMap.for_all (fun key _ -> ArgMap.find_opt key new_mono_map != None) poly_map ) new_clause_poly_map));*)
   (new_mono_map, new_clause_poly_map, new_subst_map)

let _loop_count = ref 4
let _mono_ty_args_per_fun_sym = ref { relative_bound = 1.0; absolute_cap = 50; relative_floor = 7 }
let _poly_ty_args_per_fun_sym = ref { relative_bound = 0.0; absolute_cap = 10; relative_floor = 1 }
let _mono_ty_args_per_clause = ref { relative_bound = 1000000.0; absolute_cap = 500; relative_floor = 1000000 }
let _poly_ty_args_per_clause = ref { relative_bound = 1000000.0; absolute_cap = 500; relative_floor = 1000000 }

(*neither of these are particularly useful in practice, especially the second one*)
let _ty_var_limit = ref 100000
let _subst_per_ty_var = ref 10000000
let _old_subst_per_clause = ref 1000000
let _new_subst_per_clause = ref 1000000
let _monomorphising_subst_per_clause = ref 5
let _new_clauses_relative_bound = ref 2.0
let _substitution_ordering = ref "age"
let _e_max_derived = ref 1000000

let bounds_ref =
   ref
     {
       loop_count = !_loop_count;
       mono_ty_args_per_fun_sym = !_mono_ty_args_per_fun_sym;
       poly_ty_args_per_fun_sym = !_poly_ty_args_per_fun_sym;
       mono_ty_args_per_clause = !_mono_ty_args_per_clause;
       poly_ty_args_per_clause = !_poly_ty_args_per_clause;
       (* maximum number of type variable per type in the polymorphic type arguments*)
       ty_var_limit = !_ty_var_limit;
       subst_per_ty_var = !_subst_per_ty_var;
       old_subst_per_clause = !_old_subst_per_clause;
       new_subst_per_clause = !_new_subst_per_clause;
       monomorphising_subst_per_clause = !_monomorphising_subst_per_clause;
       (* number of new clauses we generate relative to the initial number of clauses (all of them) *)
       new_clauses_relative_bound = !_new_clauses_relative_bound;
     }

(*takes a substitution map, a set of type variables to instantiate and the maximum number of authorised new substitutions*)
(* returns an iter of substitutions that instantiate all type variables *)
let generate_monomorphising_subst subst_map ty_var_iter max_new_subst =
   let ty_var_eq = HVar.equal (fun ty ty' -> ty_eq (Ty.of_term_unsafe ty) (Ty.of_term_unsafe ty')) in
   (*let ty_var_eq_old = HVar.equal InnerTerm.equal in*)
   let remaining_ty_vars ty_var_iter subst =
      Iter.diff ~eq:ty_var_eq ty_var_iter (Iter.map fst (Subst.domain subst))
   in
   (* this function essentially explores the tree of substitutions that will instantiate the type variables *)
   (* subst_acc is the current node, it instantiates all the type variables that have been removed from
    * vars_to_instantiate *)
   (* acc_iter is the iter of all previously explored leaves, they are the finished substitutions that we
    * want to keep *)
   (* acc_count is the number of substitutions we have left *)
   let rec create_subst (subst_acc, acc_iter, acc_count) vars_to_instantiate =
      if acc_count <= 0 then (acc_iter, acc_count)
      else
        (*look at the next variable to instantiate *)
        match Iter.head vars_to_instantiate with
           | None -> (Iter.singleton subst_acc, acc_count - 1)
           | Some ty_var ->
              let candidate_subst = Iter.map fst (SubstMap.find (HVar.id ty_var) subst_map) in
              (* here is where the substitution selection method is used *)
              let process_subst acc_count next_subst =
                 match Subst.merge subst_acc next_subst with
                    | exception _ -> (Iter.empty, acc_count)
                    | merged_subst ->
                       let new_vars_to_instantiate = remaining_ty_vars vars_to_instantiate merged_subst in
                          create_subst (merged_subst, Iter.empty, acc_count) new_vars_to_instantiate
              in
              let process_fold (acc_iter, acc_count) next_subst =
                 if acc_count <= 0 then (acc_iter, acc_count)
                 else
                   let res_subst, res_count = process_subst acc_count next_subst in
                      (iter_subst_union acc_iter res_subst, res_count)
              in
                 Iter.fold process_fold (Iter.empty, acc_count) candidate_subst
   in
   let res = create_subst (Subst.empty, Iter.empty, max_new_subst) ty_var_iter |> fst in
      (*Printf.printf "nb of monomorphising substitutions %i\n" (Iter.length res);*)
      Iter.persistent_lazy res

let count_arg_map arg_map =
   ArgMap.fold (fun _ (old_iter, new_iter) acc -> Iter.length old_iter + Iter.length new_iter + acc) arg_map 0

let count_arg_map_split arg_map =
   ArgMap.fold
     (fun _ (old_iter, new_iter) (old_acc, new_acc) ->
       (Iter.length old_iter + old_acc, Iter.length new_iter + new_acc))
     arg_map (0, 0)

let count_clause_arg_map clause_arg_map =
   ClauseArgMap.fold (fun _ arg_map acc -> count_arg_map arg_map + acc) clause_arg_map 0

(* takes a list of (clause_id, literal array) pairs
 * takes an integer to limit the numbers of iterations
 * returns an updated list of clauses *)
let monomorphise_problem clause_list =

   begin_time := Sys.time ();

   (*Printf.printf "\n so it begins... \n\n";*)

   (* initialisation *)
   let all_bounds = !bounds_ref in

   let loop_count = all_bounds.loop_count in

   (*Printf.printf "We start with %i total clauses\n" (List.length clause_list);*)

   (*let nb_of_lits = List.fold_left (fun acc (_, lit_arr) -> acc + Array.length lit_arr) 0 clause_list in
      Printf.printf "We start with %i total literals\n" nb_of_lits;*)

   (* create initial maps *)
   let init_mono_map, init_clause_poly_map, init_subst_map =
      List.fold_left map_initialisation_step (ArgMap.empty, ClauseArgMap.empty, PbSubstMap.empty) clause_list
   in

   (* remove polymorphic type arguments that contain type variables too many type variables (and are therefore unlikely to be instantiated) *)
   let init_clause_poly_map =
      ClauseArgMap.map
        (fun poly_map -> poly_ty_args_filter init_mono_map poly_map all_bounds.ty_var_limit)
        init_clause_poly_map
   in

   if false then (
     Printf.printf "\n here we go\n: ";
     ClauseArgMap.iter
       (fun clause_id poly_map ->
         Printf.printf "clause nb: %i\n" clause_id;
         ArgMap.iter (fun fun_sym iter -> print_all_type_args fun_sym iter) poly_map)
       init_clause_poly_map);

   (* remove duplicates *)
   (* the old iters are initialy empty (made redundant by changes in the init function *)
   let init_mono_map =
      ArgMap.map
        (fun (old_iter, new_iter) -> (Iter.empty, remove_duplicates ~eq:ty_arg_eq new_iter))
        init_mono_map
   in

   (*Printf.printf "after init %f\n" (Sys.time () -. !begin_time);*)
   let clause_is_monomorphic (_, lit_arr) = Array.for_all lit_is_monomorphic lit_arr in

   let poly_clause_list = List.filter (fun cl -> clause_is_monomorphic cl |> not) clause_list in

   if List.length poly_clause_list = 0 then
     Printf.printf
       "Warning: All polymorphic functions in this problem's clauses are instantiated,monomorphisation will \
        only consist in syntactically mangling the arguments that are types\n";
   (*Printf.printf "We begin with %i polymorphic clauses\n" (List.length poly_clause_list);*)

   let print_clause_in =
      let init_poly_clauses_count = List.length poly_clause_list in
      let init_mono_clauses_count = List.length clause_list - init_poly_clauses_count in
      Printf.printf "initial poly clauses: %i\n" init_poly_clauses_count;
      Printf.printf "initial mono clauses: %i\n" init_mono_clauses_count;
   in
   print_clause_in;
      
   (* monomorphisation loop *)
   let rec monomorphisation_loop curr_count mono_map poly_clause_map subst_map =
      (*Printf.printf "\nbegin loop %f\n" (Sys.time () -. !begin_time);*)
      (*let count_res = count_arg_map_split mono_map in*)

      (*Printf.printf "we have %i old and %i new monomorphic type args\n" (fst count_res) (snd count_res);*)
      (*Printf.printf "we have %i total polymorphic type args\n" (count_clause_arg_map poly_clause_map);*)
      (*Printf.printf "current time %f\n" (Sys.time () -. !begin_time);*)
      if curr_count <= 0 then (mono_map, poly_clause_map, subst_map)
      else
        (* given that the maps are updated independently of the clause list, we could not pass the udpated
           clauses as parameter, however, it is convienient to do so*)
        let new_subst, new_mono_map, new_poly_clause_map =
           mono_step poly_clause_list mono_map poly_clause_map subst_map curr_count all_bounds
        in
        let res = monomorphisation_loop (curr_count - 1) new_mono_map new_poly_clause_map new_subst in
           res
   in

   let _, _, subst_map_res =
      (* TODO check rigorously if persistent or persistent lazy is best (perhaps nothing at all but i doubt it) *)
      let init_mono_map =
         ArgMap.map
           (fun (old_iter, new_iter) -> (Iter.persistent old_iter, Iter.persistent new_iter))
           init_mono_map
      in
         monomorphisation_loop loop_count init_mono_map init_clause_poly_map init_subst_map
   in

   let var_eq = HVar.equal (fun _ _ -> true) in
   let clause_ty_vars lit_arr =
      (*Printf.printf "lit_arr length %i\n" (Array.length lit_arr);*)
      (* TODO check that this persistent lazy is worth it *)
      let all_vars =
         remove_duplicates ~eq:var_eq
           (Iter.persistent_lazy
              (Iter.flat_map
                 (fun lit -> (Literal.Seq.vars lit :> InnerTerm.t HVar.t Iter.t))
                 (Iter.of_array lit_arr)))
      in
         Iter.filter (fun var -> InnerTerm.equal (HVar.ty var) InnerTerm.tType) all_vars
   in

   let instantiate_clause subst_map (clause_id, lit_arr) new_clauses_remaining =
      let vars_to_instantiate = clause_ty_vars lit_arr in
      (* TODO check that monomorphising subst is possible in the first place *)
      let subst_map_filter_age subst_map iteration_count =
         SubstMap.map
           (fun subst_iter -> Iter.filter (fun (subst, age) -> age = iteration_count) subst_iter)
           subst_map
      in
      (* the function is written somewhat awkwardly because we want to generate the substitutions of the first iter first *)
      let rec all_mono_subst curr_iter total_subst_nb =
         if curr_iter < 0 then Iter.empty
         else
           let prev_subst = all_mono_subst (curr_iter - 1) total_subst_nb in
              if Iter.length prev_subst >= total_subst_nb then prev_subst
              else
                (* TODO sort out which kind of substitution ordering we want*)

                let ordered_subst_map =
                   if !_substitution_ordering = "age" then subst_map_filter_age subst_map curr_iter
                   else if !_substitution_ordering = "random" then
                   let rand_subst_map =
                      SubstMap.map
                        (fun subst_iter ->
                          Iter.sort_uniq
                            ~cmp:(fun _ _ -> if Random.bool () then if Random.bool () then 1 else 0 else -1)
                            subst_iter)
                        subst_map in
                      rand_subst_map
                   else if !_substitution_ordering = "arbitrary" then subst_map
                   else assert false
               in
                
                let curr_subst =
                   generate_monomorphising_subst ordered_subst_map vars_to_instantiate all_bounds.monomorphising_subst_per_clause
                in
                let curr_subst' = iter_truncate (total_subst_nb - Iter.length prev_subst) curr_subst in
                   remove_duplicates ~eq:Subst.equal (Iter.append prev_subst curr_subst')
      in
      let mono_subst = all_mono_subst all_bounds.loop_count new_clauses_remaining in

      (*Printf.printf "We have %i monomorphising substitutions\n" (Iter.length mono_subst);*)
      let apply_subst subst lit_arr = Array.map (fun lit -> apply_subst_lit lit subst) lit_arr in
      (* need to make more thourough checks to see if this persistent_lazy is worth it *)
      let new_lits_iter = Iter.map (fun subst -> apply_subst subst lit_arr) (Iter.persistent_lazy mono_subst) in
         Iter.map (fun lit_arr -> (clause_id, lit_arr)) new_lits_iter
   in

   let new_clauses_fold (acc_cl, acc_remaining) (clause_id, lit_arr) =
      if acc_remaining <= 0 then (acc_cl, acc_remaining)
      else
        let new_clauses =
           instantiate_clause (PbSubstMap.find clause_id subst_map_res) (clause_id, lit_arr) acc_remaining
        in
        let new_remaining = acc_remaining - Iter.length new_clauses in
           (Iter.append acc_cl (iter_truncate acc_remaining new_clauses), new_remaining)
   in
   (*Printf.printf "\nfinished generating types %f\n" (Sys.time () -. !begin_time);*)
   
   let total_clause_limit =
      max !_e_max_derived (int_of_float (all_bounds.new_clauses_relative_bound *. float_of_int (List.length clause_list)))
   in

   let new_clauses, _ = List.fold_left new_clauses_fold (Iter.empty, total_clause_limit) poly_clause_list in

   let clause_eq (_, cl) (_, cl') =
      if Array.length cl = Array.length cl' then Array.for_all2 Literal.equal cl cl' else false
   in

   let new_clauses = remove_duplicates ~eq:clause_eq new_clauses in

   let mono_clauses = List.filter clause_is_monomorphic clause_list in
   (*let mono_clauses = List.filteri (fun i _ -> i <= 0) mono_clauses in*)
   (*Printf.printf "We have %i MONOMORPHIC clauses\n" (List.length mono_clauses);*)
   (*List.iter (fun (_, lit_arr) -> Printf.printf "clause %s\n" (Literals.to_string lit_arr)) mono_clauses;*)
   let new_clause_list = Iter.to_list new_clauses @ mono_clauses in
   (*let new_clause_list = [] in*)

   (*Printf.printf "generating all clauses %f\n" (Sys.time () -. !begin_time);*)
   (*Printf.printf "all new clauses %i\n" (List.length clause_list - List.length mono_clauses);*)

   let subst_count pb_subst_map =
      PbSubstMap.fold (fun _ subst_map acc ->
          acc + SubstMap.fold (fun _ subst_iter acc -> acc + Iter.length subst_iter) subst_map 0) pb_subst_map 0
   in
   (* we want to have; monomorphisation time, number of initial poly and mono clauses, number of output clauses*)
   let print_end_info =
      let new_clause_count = Iter.length new_clauses in
      let all_new_subst = subst_count subst_map_res in
      let mono_time = Sys.time () -. !begin_time in
         Printf.printf "\nmonomorphisation time: %f\n" mono_time;
         Printf.printf "new clauses: %i\n" new_clause_count;
         Printf.printf "all final substitutions: %i\n" all_new_subst;
   in

   print_end_info;
   new_clause_list

let rec convert_type ty =
   let open Ty in
   let args = expected_args ty in
   let ret = returns ty in
      if args != [] then List.map convert_type args ==> convert_type ret
      else
        match view ty with
           | Builtin _ -> ty 
           | _ -> Ty.const (ID.make (Ty.mangle ty))

let () =
   Options.add_opts
     [
        ("--mono-ty-args", Arg.String (fun s ->
           match String.split_on_char ',' s with
            | [cap;mult;floor] ->
               _mono_ty_args_per_fun_sym := { relative_bound = float_of_string mult; absolute_cap = int_of_string cap; relative_floor = int_of_string floor }
            | _ -> failwith "invalid mono ty args options"),
            " parameters for controlling the number of new monomorphic type argument for each function symbol per iteration");
        ("--poly-ty-args", Arg.String (fun s ->
           match String.split_on_char ',' s with
            | [cap;mult;floor] ->
               _poly_ty_args_per_fun_sym := { relative_bound = float_of_string mult; absolute_cap = int_of_string cap; relative_floor = int_of_string floor }
            | _ -> failwith "invalid poly ty args options"),
            " parameters for controlling the number of new polymorphic type argument for each function symbol perclause per iteration");
       ("--mono-loop", Arg.Int (( := ) _loop_count), " number of iterations of the monomorphisation algorithm");
       ( "--ty-var-limit",
         Arg.Int (( := ) _ty_var_limit),
         " maximum number of type variables a clause can contain for monomorphisation" );
       ( "--old-subst-per-clause",
         Arg.Int (( := ) _old_subst_per_clause),
         " maximum number of substitutions generated from matching old polymorphic type arguments with new \
          monomorphic type arguments per clause per iteration of the monomorphisation algorithm" );
       ( "--new-subst-per-clause",
         Arg.Int (( := ) _new_subst_per_clause),
         " maximum number of substitutions generated from matching new polymorphic type arguments with \
          monomorphic type arguments per clause per iteration of the monomorphisation algortihm" );
       ( "--subst-per-ty-var",
         Arg.Int (( := ) _subst_per_ty_var),
         " maximum number of substitutions that instantiate a type variable in a clause for each iteration of \
          the monomorphisation algorithm" );
       ( "--new-clauses-multiplier",
         Arg.Float (( := ) _new_clauses_relative_bound),
         " maximum number of new clauses the monomorphisation algorithm will generate, expressed as a factor of \
          the initial number of clauses destined for monomorphisation" );
       ( "--monomorphising-subst-per-clause",
         Arg.Int (( := ) _monomorphising_subst_per_clause),
         " maximum number of instantiating substitutions that can be generated by monomorphisation algorithm \
          per clause per iteration" );
      ( "--substitution-ordering",
         Arg.String (fun s ->
             match s with
                | "random" -> ()
                | "age" -> ()
                | "arbitrary" -> ()
                | _ -> failwith "invalid substitution ordering"),
         " substitution ordering used at the clause generation phase of the monomorphisation algorithm" );
       ( "--e-max-derived",
         (* TODO if this is greater than _max_derived, print warning that we are creating superfluous clauses *)
         Arg.Set_int _e_max_derived,
         " set the limit of clauses that are derived by Zipperposition and given to E" );
     ]
