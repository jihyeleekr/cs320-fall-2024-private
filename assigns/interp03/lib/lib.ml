open Utils
include My_parser

let unify (ty : ty) (constrs : constr list) : ty_scheme option =
  let rec unify_types ty1 ty2 subst =
    match (ty1, ty2) with
    | TVar x, TVar y when x = y -> Some subst
    | TVar x, _ ->
        (match List.assoc_opt x subst with
         | None -> Some ((x, ty2) :: subst)
         | Some bound_ty -> unify_types bound_ty ty2 subst)
    | _, TVar y ->
        (match List.assoc_opt y subst with
         | None -> Some ((y, ty1) :: subst)
         | Some bound_ty -> unify_types ty1 bound_ty subst)
    | TFun (t1, t2), TFun (t1', t2') ->
        (match unify_types t1 t1' subst with
         | Some subst' -> unify_types t2 t2' subst'
         | None -> None)
    | TList t1, TList t2 -> unify_types t1 t2 subst
    | TOption t1, TOption t2 -> unify_types t1 t2 subst
    | TPair (t1, t2), TPair (t1', t2') ->
        (match unify_types t1 t1' subst with
         | Some subst' -> unify_types t2 t2' subst'
         | None -> None)
    | TUnit, TUnit
    | TInt, TInt
    | TFloat, TFloat
    | TBool, TBool -> Some subst
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
  | Int _ -> Some (Forall ([], TInt))
  | Float _ -> Some (Forall ([], TFloat))
  | True | False -> Some (Forall ([], TBool))
  | Var x -> Env.find_opt x env
  | Fun (arg, _, body) ->
      let arg_ty = TVar (gensym ()) in
      let new_env = Env.add arg (Forall ([], arg_ty)) env in
      (match type_of new_env body with
       | Some (Forall (qs, body_ty)) -> Some (Forall (qs, TFun (arg_ty, body_ty)))
       | None -> None)
  | App (f, arg) ->
      (match type_of env f, type_of env arg with
       | Some (Forall (_, TFun (param_ty, ret_ty))), Some (Forall (_, arg_ty))
         when param_ty = arg_ty -> Some (Forall ([], ret_ty))
       | _ -> None)
  | Let { is_rec = _is_rec; name; value; body } ->
      (match type_of env value with
       | Some scheme ->
           let new_env = Env.add name scheme env in
           type_of new_env body
       | None -> None)
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
