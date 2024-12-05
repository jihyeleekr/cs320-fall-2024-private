open Utils
include My_parser

let unify (ty : ty) (constrs : constr list) : ty_scheme option =
  let rec occurs_check x ty subst =
    let rec exists p = function
      | [] -> false
      | y :: ys -> p y || exists p ys
    in
    match ty with
    | TVar y -> y = x || exists (fun (_, t) -> occurs_check x t subst) subst
    | TFun (t1, t2) -> occurs_check x t1 subst || occurs_check x t2 subst
    | TList t | TOption t -> occurs_check x t subst
    | TPair (t1, t2) -> occurs_check x t1 subst || occurs_check x t2 subst
    | _ -> false
  in

  let rec unify_types ty1 ty2 subst =
    match (ty1, ty2) with
    | TVar x, TVar y when x = y -> Some subst
    | TVar x, t | t, TVar x ->
        if occurs_check x t subst then None
        else Some ((x, t) :: subst)
    | TFun (t1, t2), TFun (t1', t2') ->
        (match unify_types t1 t1' subst with
         | Some subst' -> unify_types t2 t2' subst'
         | None -> None)
    | TList t1, TList t2 | TOption t1, TOption t2 -> unify_types t1 t2 subst
    | TPair (t1, t2), TPair (t1', t2') ->
        (match unify_types t1 t1' subst with
         | Some subst' -> unify_types t2 t2' subst'
         | None -> None)
    | TUnit, TUnit | TInt, TInt | TFloat, TFloat | TBool, TBool -> Some subst
    | _, _ -> None
  in

  let rec apply_subst subst ty =
    match ty with
    | TVar x -> (match List.assoc_opt x subst with Some t -> t | None -> ty)
    | TFun (t1, t2) -> TFun (apply_subst subst t1, apply_subst subst t2)
    | TList t -> TList (apply_subst subst t)
    | TOption t -> TOption (apply_subst subst t)
    | TPair (t1, t2) -> TPair (apply_subst subst t1, apply_subst subst t2)
    | _ -> ty
  in

  let rec solve_constraints constrs subst =
    match constrs with
    | [] -> Some subst
    | (t1, t2) :: rest ->
        (match unify_types t1 t2 subst with
         | Some subst' -> solve_constraints rest subst'
         | None -> None)
  in

  match solve_constraints constrs [] with
  | Some subst ->
      let generalized_ty = apply_subst subst ty in
      Some (Forall ([], generalized_ty))
  | None -> None


  let rec type_of (env : stc_env) (expr : expr) : ty_scheme option =
    match expr with
    (* Literals *)
    | Int _ -> Some (Forall ([], TInt))
    | Float _ -> Some (Forall ([], TFloat))
    | True | False -> Some (Forall ([], TBool))
    | Unit -> Some (Forall ([], TUnit))
    | Var x -> Env.find_opt x env
  
    (* Functions *)
    | Fun (arg, _, body) ->
        let arg_ty = TVar (gensym ()) in
        let new_env = Env.add arg (Forall ([], arg_ty)) env in
        (match type_of new_env body with
         | Some (Forall (qs, body_ty)) -> Some (Forall (qs, TFun (arg_ty, body_ty)))
         | None -> None)
  
    (* Function Applications *)
    | App (f, arg) ->
        (match type_of env f, type_of env arg with
         | Some (Forall (_, TFun (param_ty, ret_ty))), Some (Forall (_, arg_ty))
           when param_ty = arg_ty ->
             Some (Forall ([], ret_ty))
         | _ -> None)
  
    (* Let Bindings *)
    | Let { is_rec = false; name; value; body } ->
        (match type_of env value with
         | Some scheme ->
             let new_env = Env.add name scheme env in
             type_of new_env body
         | None -> None)
    | Let { is_rec = true; name; value; body } ->
        (match value with
         | Fun (arg, _, body_fun) ->
             let arg_ty = TVar (gensym ()) in
             let ret_ty = TVar (gensym ()) in
             let fun_ty = TFun (arg_ty, ret_ty) in
             let new_env = Env.add name (Forall ([], fun_ty)) env in
             let body_env = Env.add arg (Forall ([], arg_ty)) new_env in
             (match type_of body_env body_fun with
              | Some (Forall (_, inferred_ret_ty)) when inferred_ret_ty = ret_ty ->
                  type_of new_env body
              | _ -> None)
         | _ -> None)
  
    (* If Expressions *)
    | If (cond, then_branch, else_branch) ->
        (match type_of env cond, type_of env then_branch, type_of env else_branch with
         | Some (Forall (_, TBool)), Some (Forall (_, tau1)), Some (Forall (_, tau2))
           when tau1 = tau2 ->
             Some (Forall ([], tau1))
         | _ -> None)
  
    (* Option Match *)
    | OptMatch { matched; some_name; some_case; none_case } ->
        (match type_of env matched with
         | Some (Forall (_, TOption tau)) ->
             let env_some = Env.add some_name (Forall ([], tau)) env in
             (match type_of env_some some_case, type_of env none_case with
              | Some (Forall (_, tau1)), Some (Forall (_, tau2)) when tau1 = tau2 ->
                  Some (Forall ([], tau1))
              | _ -> None)
         | _ -> None)
  
    (* List Match *)
    | ListMatch { matched; hd_name; tl_name; cons_case; nil_case } ->
        (match type_of env matched with
         | Some (Forall (_, TList tau)) ->
             let env_cons = Env.add hd_name (Forall ([], tau)) (Env.add tl_name (Forall ([], TList tau)) env) in
             (match type_of env_cons cons_case, type_of env nil_case with
              | Some (Forall (_, tau1)), Some (Forall (_, tau2)) when tau1 = tau2 ->
                  Some (Forall ([], tau1))
              | _ -> None)
         | _ -> None)
  
    (* Pair Match *)
    | PairMatch { matched; fst_name; snd_name; case } ->
        (match type_of env matched with
         | Some (Forall (_, TPair (tau1, tau2))) ->
             let env_pair = Env.add fst_name (Forall ([], tau1)) (Env.add snd_name (Forall ([], tau2)) env) in
             type_of env_pair case
         | _ -> None)
  
    (* Type Annotations *)
    | Annot (e, ty) ->
        (match type_of env e with
         | Some (Forall (_, tau)) when tau = ty -> Some (Forall ([], ty))
         | _ -> None)
  
    (* Operators *)
    | Bop (op, e1, e2) ->
        (match op with
         | Add | Sub | Mul | Div | Mod ->
             (match type_of env e1, type_of env e2 with
              | Some (Forall (_, TInt)), Some (Forall (_, TInt)) ->
                  Some (Forall ([], TInt))
              | _ -> None)
         | AddF | SubF | MulF | DivF | PowF ->
             (match type_of env e1, type_of env e2 with
              | Some (Forall (_, TFloat)), Some (Forall (_, TFloat)) ->
                  Some (Forall ([], TFloat))
              | _ -> None)
         | And | Or ->
             (match type_of env e1, type_of env e2 with
              | Some (Forall (_, TBool)), Some (Forall (_, TBool)) ->
                  Some (Forall ([], TBool))
              | _ -> None)
         | Lt | Lte | Gt | Gte | Eq | Neq ->
             (match type_of env e1, type_of env e2 with
              | Some (Forall (_, tau1)), Some (Forall (_, tau2)) when tau1 = tau2 ->
                  Some (Forall ([], TBool))
              | _ -> None)
         | Concat ->
             (match type_of env e1, type_of env e2 with
              | Some (Forall (_, TList tau1)), Some (Forall (_, TList tau2))
                when tau1 = tau2 ->
                  Some (Forall ([], TList tau1))
              | _ -> None)
         | Cons ->
             (match type_of env e1, type_of env e2 with
              | Some (Forall (_, tau1)), Some (Forall (_, TList tau2))
                when tau1 = tau2 ->
                  Some (Forall ([], TList tau1))
              | _ -> None)
         | Comma -> None
         )
    | _ -> None

exception AssertFail
exception DivByZero
exception RecWithoutArg
exception CompareFunVals

let rec eval_expr (env : dyn_env) (expr : expr) : value =
  match expr with
  | Unit -> VUnit
  | True -> VBool true
  | False -> VBool false
  | Int n -> VInt n
  | Float f -> VFloat f
  | Var x -> (try Env.find x env with Not_found -> assert false)
  | Assert e ->
      (match eval_expr env e with
       | VBool true -> VUnit
       | VBool false -> raise AssertFail
       | _ -> assert false)
  | Fun (arg, _, body) -> VClos { name = None; arg; body; env }
  | App (f, arg) ->
      (match eval_expr env f with
       | VClos { name = _; arg = param; body; env = closure_env } ->
           let arg_val = eval_expr env arg in
           eval_expr (Env.add param arg_val closure_env) body
       | _ -> assert false)
  | Let { is_rec = _is_rec; name; value; body } ->
      let value_val = eval_expr env value in
      eval_expr (Env.add name value_val env) body
  | _ -> assert false

let type_check =
  let rec go ctxt = function
  | [] -> Some (Forall ([], TUnit))
  | {is_rec;name;value} :: ls ->
    match type_of ctxt (Let {is_rec;name;value; body = Var name}) with
    | Some ty -> (
      match ls with
      | [] -> Some ty
      | _ ->
        let ctxt = Env.add name ty ctxt in
        go ctxt ls
    )
    | None -> None
  in go Env.empty

let eval p =
  let rec nest = function
    | [] -> Unit
    | [{is_rec;name;value}] -> Let {is_rec;name;value;body = Var name}
    | {is_rec;name;value} :: ls -> Let {is_rec;name;value;body = nest ls}
  in eval_expr Env.empty (nest p)

let interp input =
  match parse input with
  | Some prog -> (
    match type_check prog with
    | Some ty -> Ok (eval prog, ty)
    | None -> Error TypeError
  )
  | None -> Error ParseError
