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
    | Unit -> Some (Forall ([], TUnit))
    | True | False -> Some (Forall ([], TBool))
    | Int _ -> Some (Forall ([], TInt))
    | Float _ -> Some (Forall ([], TFloat))
    | Var x ->
        (match Env.find_opt x env with
         | Some ty_scheme -> Some ty_scheme
         | None -> None) 
  
    | Fun (arg, annot, body) ->
        let arg_ty = match annot with
          | Some ty -> ty
          | None -> TVar (gensym ())
        in
        let new_env = Env.add arg (Forall ([], arg_ty)) env in
        (match type_of new_env body with
         | Some (Forall (qs, body_ty)) -> Some (Forall (qs, TFun (arg_ty, body_ty)))
         | None -> None)
  
    | App (f, arg) ->
        (match type_of env f, type_of env arg with
         | Some (Forall (_, TFun (param_ty, ret_ty))), Some (Forall (_, arg_ty)) ->
             if param_ty = arg_ty then Some (Forall ([], ret_ty))
             else None 
         | _ -> None)
  
    | Annot (expr, annot_ty) ->
        (match type_of env expr with
         | Some (Forall (_, expr_ty)) when expr_ty = annot_ty -> Some (Forall ([], annot_ty))
         | _ -> None)
  
    | If (cond, then_branch, else_branch) ->
        (match type_of env cond, type_of env then_branch, type_of env else_branch with
         | Some (Forall (_, TBool)), Some (Forall (_, then_ty)), Some (Forall (_, else_ty)) ->
             if then_ty = else_ty then Some (Forall ([], then_ty))
             else None
         | _ -> None)
  
    | Let { is_rec; name; value; body } ->
        (match is_rec, value with
         | false, _ ->
             (match type_of env value with
              | Some scheme ->
                  let new_env = Env.add name scheme env in
                  type_of new_env body
              | None -> None)
         | true, Fun (arg, _, body_fun) ->
             let arg_ty = TVar (gensym ()) in
             let ret_ty = TVar (gensym ()) in
             let func_ty = TFun (arg_ty, ret_ty) in
             let new_env = Env.add name (Forall ([], func_ty)) env in
             (match type_of (Env.add arg (Forall ([], arg_ty)) new_env) body_fun with
              | Some (Forall (_, ret_ty')) ->
                  if ret_ty = ret_ty' then type_of new_env body else None
              | None -> None)
         | true, _ -> None )
  
    | OptMatch { matched; some_name; some_case; none_case } ->
        (match type_of env matched with
         | Some (Forall (_, TOption opt_ty)) ->
             let new_env = Env.add some_name (Forall ([], opt_ty)) env in
             (match type_of new_env some_case, type_of env none_case with
              | Some (Forall (_, some_ty)), Some (Forall (_, none_ty)) when some_ty = none_ty ->
                  Some (Forall ([], some_ty))
              | _ -> None)
         | _ -> None)
  
    | ListMatch { matched; hd_name; tl_name; cons_case; nil_case } ->
        (match type_of env matched with
         | Some (Forall (_, TList elem_ty)) ->
             let new_env = Env.add hd_name (Forall ([], elem_ty)) (Env.add tl_name (Forall ([], TList elem_ty)) env) in
             (match type_of new_env cons_case, type_of env nil_case with
              | Some (Forall (_, cons_ty)), Some (Forall (_, nil_ty)) when cons_ty = nil_ty ->
                  Some (Forall ([], cons_ty))
              | _ -> None)
         | _ -> None)
  
    | PairMatch { matched; fst_name; snd_name; case } ->
        (match type_of env matched with
         | Some (Forall (_, TPair (fst_ty, snd_ty))) ->
             let new_env = Env.add fst_name (Forall ([], fst_ty)) (Env.add snd_name (Forall ([], snd_ty)) env) in
             type_of new_env case
         | _ -> None)
  
    | Nil -> Some (Forall ([], TList (TVar (gensym ()))))
    | ENone -> Some (Forall ([], TOption (TVar (gensym ())))) 
    | ESome e ->
        (match type_of env e with
         | Some (Forall (_, elem_ty)) -> Some (Forall ([], TOption elem_ty))
         | _ -> None)
  
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
  | ENone -> VNone
  | ESome e -> VSome (eval_expr env e)
  | OptMatch { matched; some_name; some_case; none_case } ->
      (match eval_expr env matched with
       | VSome v -> eval_expr (Env.add some_name v env) some_case
       | VNone -> eval_expr env none_case
       | _ -> assert false)
  | Nil -> VList []
  | Bop (Cons, hd, tl) ->
      (match eval_expr env tl with
       | VList lst -> VList (eval_expr env hd :: lst)
       | _ -> assert false)
  | ListMatch { matched; hd_name; tl_name; cons_case; nil_case } ->
      (match eval_expr env matched with
       | VList (hd :: tl) ->
           let env' = Env.add hd_name hd (Env.add tl_name (VList tl) env) in
           eval_expr env' cons_case
       | VList [] -> eval_expr env nil_case
       | _ -> assert false)
  | Bop (Comma, e1, e2) ->
      let v1 = eval_expr env e1 in
      let v2 = eval_expr env e2 in
      VPair (v1, v2)
  | PairMatch { matched; fst_name; snd_name; case } ->
      (match eval_expr env matched with
       | VPair (v1, v2) ->
           let env' = Env.add fst_name v1 (Env.add snd_name v2 env) in
           eval_expr env' case
       | _ -> assert false)
  | Bop (op, e1, e2) ->
      let v1 = eval_expr env e1 in
      let v2 = eval_expr env e2 in
      (match (op, v1, v2) with
       | (Add, VInt n1, VInt n2) -> VInt (n1 + n2)
       | (Sub, VInt n1, VInt n2) -> VInt (n1 - n2)
       | (Mul, VInt n1, VInt n2) -> VInt (n1 * n2)
       | (Div, VInt n1, VInt n2) -> if n2 = 0 then raise DivByZero else VInt (n1 / n2)
       | (Mod, VInt n1, VInt n2) -> if n2 = 0 then raise DivByZero else VInt (n1 mod n2)
       | (AddF, VFloat f1, VFloat f2) -> VFloat (f1 +. f2)
       | (SubF, VFloat f1, VFloat f2) -> VFloat (f1 -. f2)
       | (MulF, VFloat f1, VFloat f2) -> VFloat (f1 *. f2)
       | (DivF, VFloat f1, VFloat f2) -> if f2 = 0. then raise DivByZero else VFloat (f1 /. f2)
       | (PowF, VFloat f1, VFloat f2) -> VFloat (f1 ** f2)
       | (Eq, VClos _, _) | (Eq, _, VClos _) -> raise CompareFunVals
       | (Eq, v1, v2) -> VBool (v1 = v2)
       | (Neq, VClos _, _) | (Neq, _, VClos _) -> raise CompareFunVals
       | (Neq, v1, v2) -> VBool (v1 <> v2)
       | (Lt, VClos _, _) | (Lt, _, VClos _) -> raise CompareFunVals
       | (Lt, v1, v2) -> VBool (v1 < v2)
       | (Lte, VClos _, _) | (Lte, _, VClos _) -> raise CompareFunVals
       | (Lte, v1, v2) -> VBool (v1 <= v2)
       | (Gt, VClos _, _) | (Gt, _, VClos _) -> raise CompareFunVals
       | (Gt, v1, v2) -> VBool (v1 > v2)
       | (Gte, VClos _, _) | (Gte, _, VClos _) -> raise CompareFunVals
       | (Gte, v1, v2) -> VBool (v1 >= v2)
       | (And, VBool b1, _) -> if not b1 then VBool false else eval_expr env e2
       | (Or, VBool b1, _) -> if b1 then VBool true else eval_expr env e2
       | _ -> assert false)
  | If (cond, then_branch, else_branch) ->
      (match eval_expr env cond with
       | VBool true -> eval_expr env then_branch
       | VBool false -> eval_expr env else_branch
       | _ -> assert false)
  | Fun (arg, _, body) -> VClos { name = None; arg; body; env }
  | App (f, arg) ->
      (match eval_expr env f with
       | VClos { name = _; arg = param; body; env = closure_env } ->
           let arg_val = eval_expr env arg in
           eval_expr (Env.add param arg_val closure_env) body
       | _ -> assert false)
  | Let { is_rec = false; name; value; body } ->
      let value_val = eval_expr env value in
      eval_expr (Env.add name value_val env) body
  | Let { is_rec = true; name; value; body } ->
      (match value with
       | Fun (arg, _, body_fun) ->
           let rec_env = Env.add name (VClos { name = Some name; arg; body = body_fun; env }) env in
           eval_expr rec_env body
       | _ -> raise RecWithoutArg)
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