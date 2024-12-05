open Utils
include My_parser

(* Helper Functions *)
let rec occurs x ty =
  match ty with
  | TVar y -> x = y
  | TFun (t1, t2) | TPair (t1, t2) -> occurs x t1 || occurs x t2
  | TList t | TOption t -> occurs x t
  | _ -> false

let rec apply_subst subst ty =
  match ty with
  | TVar x -> (try List.assoc x subst with Not_found -> ty)
  | TFun (t1, t2) -> TFun (apply_subst subst t1, apply_subst subst t2)
  | TPair (t1, t2) -> TPair (apply_subst subst t1, apply_subst subst t2)
  | TList t -> TList (apply_subst subst t)
  | TOption t -> TOption (apply_subst subst t)
  | _ -> ty

let apply_subst_to_constraints subst constraints =
  List.map (fun (t1, t2) -> (apply_subst subst t1, apply_subst subst t2)) constraints

(* unify Function *)
let rec unify ty constraints =
  match constraints with
  | [] -> Some (Forall ([], ty)) 
  | (t1, t2) :: rest when t1 = t2 -> unify ty rest 
  | (TVar x, t) :: rest | (t, TVar x) :: rest ->
    if occurs x t then None 
    else
      let subst = [(x, t)] in
      (match unify (apply_subst subst ty) (apply_subst_to_constraints subst rest) with
       | Some (Forall (vars, unified_ty)) ->
         let subst_ty = apply_subst subst unified_ty in
         Some (Forall (vars, subst_ty))
       | None -> None)
  | (TFun (t1a, t1b), TFun (t2a, t2b)) :: rest ->
    unify ty ((t1a, t2a) :: (t1b, t2b) :: rest)
  | (TPair (t1a, t1b), TPair (t2a, t2b)) :: rest ->
    unify ty ((t1a, t2a) :: (t1b, t2b) :: rest)
  | (TList t1, TList t2) :: rest | (TOption t1, TOption t2) :: rest ->
    unify ty ((t1, t2) :: rest)
  | (TInt, TFloat) :: _ | (TFloat, TInt) :: _ -> None 
  | (TBool, TInt) :: _ | (TBool, TFloat) :: _ -> None 
  | _ -> None 



(* type_of Function *)
let rec type_of env expr =
  match expr with
  | Unit -> Some (Forall ([], TUnit))
  | True | False -> Some (Forall ([], TBool))
  | Int _ -> Some (Forall ([], TInt))
  | Float _ -> Some (Forall ([], TFloat))
  | Var x -> Env.find_opt x env
  | Fun (arg, ty_opt, body) ->
    let arg_ty = match ty_opt with Some ty -> ty | None -> TVar (gensym ()) in
    let env' = Env.add arg (Forall ([], arg_ty)) env in
    (match type_of env' body with
     | Some (Forall ([], body_ty)) -> Some (Forall ([], TFun (arg_ty, body_ty)))
     | _ -> None)
  | App (f, arg) ->
    (match type_of env f, type_of env arg with
      | Some (Forall (_, TFun (param_ty, ret_ty))), Some (Forall (_, arg_ty))
        when param_ty = arg_ty -> Some (Forall ([], ret_ty))
      | _ -> None)
  | If (cond, e1, e2) ->
    (match type_of env cond, type_of env e1, type_of env e2 with
     | Some (Forall ([], TBool)), Some (Forall ([], t1)), Some (Forall ([], t2)) ->
       let constraints = [(t1, t2)] in
       (match unify t1 constraints with
        | Some (Forall (_, ty)) -> Some (Forall ([], ty))
        | None -> None)
     | _ -> None)
  | Bop (op, e1, e2) ->
    (match op with
     | Add | Sub | Mul | Div | Mod ->
       let ty_int = TInt in
       (match type_of env e1, type_of env e2 with
        | Some (Forall ([], t1)), Some (Forall ([], t2)) ->
          let constraints = [(t1, ty_int); (t2, ty_int)] in
          (match unify ty_int constraints with
           | Some (Forall (_, ty)) -> Some (Forall ([], ty))
           | None -> None)
        | _ -> None)
     | AddF | SubF | MulF | DivF | PowF ->
       let ty_float = TFloat in
       (match type_of env e1, type_of env e2 with
        | Some (Forall ([], t1)), Some (Forall ([], t2)) ->
          let constraints = [(t1, ty_float); (t2, ty_float)] in
          (match unify ty_float constraints with
           | Some (Forall (_, ty)) -> Some (Forall ([], ty))
           | None -> None)
        | _ -> None)
     | _ -> None) 
  | ListMatch { matched; hd_name; tl_name; cons_case; nil_case } ->
    let elem_ty = TVar (gensym ()) in
    let list_ty = TList elem_ty in
    (match type_of env matched, type_of (Env.add hd_name (Forall ([], elem_ty))
                                        (Env.add tl_name (Forall ([], list_ty)) env)) cons_case, type_of env nil_case with
     | Some (Forall ([], t_matched)), Some (Forall ([], t_cons)), Some (Forall ([], t_nil)) ->
       let constraints = [(t_matched, list_ty); (t_cons, t_nil)] in
       (match unify t_cons constraints with
        | Some (Forall (_, ty)) -> Some (Forall ([], ty))
        | None -> None)
     | _ -> None)
  | OptMatch { matched; some_name; some_case; none_case } ->
    let elem_ty = TVar (gensym ()) in
    let opt_ty = TOption elem_ty in
    (match type_of env matched, type_of (Env.add some_name (Forall ([], elem_ty)) env) some_case, type_of env none_case with
     | Some (Forall ([], t_matched)), Some (Forall ([], t_some)), Some (Forall ([], t_none)) ->
       let constraints = [(t_matched, opt_ty); (t_some, t_none)] in
       (match unify t_some constraints with
        | Some (Forall (_, ty)) -> Some (Forall ([], ty))
        | None -> None)
     | _ -> None)
  | PairMatch { matched; fst_name; snd_name; case } ->
    let fst_ty = TVar (gensym ()) in
    let snd_ty = TVar (gensym ()) in
    let pair_ty = TPair (fst_ty, snd_ty) in
    (match type_of env matched, type_of (Env.add fst_name (Forall ([], fst_ty))
                                        (Env.add snd_name (Forall ([], snd_ty)) env)) case with
     | Some (Forall ([], t_matched)), Some (Forall ([], t_case)) ->
       let constraints = [(t_matched, pair_ty)] in
       (match unify t_case constraints with
        | Some (Forall (_, ty)) -> Some (Forall ([], ty))
        | None -> None)
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
  | Var x ->
      (try Env.find x env
       with Not_found -> assert false )
  | Assert e ->
      (match eval_expr env e with
       | VBool true -> VUnit
       | VBool false -> raise AssertFail
       | _ -> assert false )
  | ENone -> VNone
  | ESome e -> VSome (eval_expr env e)
  | OptMatch { matched; some_name; some_case; none_case } ->
      (match eval_expr env matched with
       | VSome v -> eval_expr (Env.add some_name v env) some_case
       | VNone -> eval_expr env none_case
       | _ -> assert false )
  | Nil -> VList []
  | Bop (Cons, hd, tl) ->
      (match eval_expr env tl with
       | VList lst -> VList (eval_expr env hd :: lst)
       | _ -> assert false )
  | ListMatch { matched; hd_name; tl_name; cons_case; nil_case } ->
      (match eval_expr env matched with
       | VList (hd :: tl) ->
           let env' = Env.add hd_name hd (Env.add tl_name (VList tl) env) in
           eval_expr env' cons_case
       | VList [] -> eval_expr env nil_case
       | _ -> assert false )
  | Bop (Comma, e1, e2) ->
      let v1 = eval_expr env e1 in
      let v2 = eval_expr env e2 in
      VPair (v1, v2)
  | PairMatch { matched; fst_name; snd_name; case } ->
      (match eval_expr env matched with
       | VPair (v1, v2) ->
           let env' = Env.add fst_name v1 (Env.add snd_name v2 env) in
           eval_expr env' case
       | _ -> assert false )
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
       | (DivF, VFloat f1, VFloat f2) -> if f2 = 0.0 then raise DivByZero else VFloat (f1 /. f2)
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
       | (And, VBool b1, VBool b2) -> VBool (b1 && b2)
       | (Or, VBool b1, VBool b2) -> VBool (b1 || b2)
       | _ -> assert false )
  | If (cond, then_branch, else_branch) ->
      (match eval_expr env cond with
       | VBool true -> eval_expr env then_branch
       | VBool false -> eval_expr env else_branch
       | _ -> assert false )
  | Fun (arg, _, body) -> VClos { name = None; arg; body; env }
  | App (f, arg) ->
      (match eval_expr env f with
       | VClos { name = _; arg = param; body; env = closure_env } ->
           let arg_val = eval_expr env arg in
           eval_expr (Env.add param arg_val closure_env) body
       | _ -> assert false )
  | Let { is_rec = false; name; value; body } ->
      let value_val = eval_expr env value in
      eval_expr (Env.add name value_val env) body
  | Let { is_rec = true; name; value; body } ->
      (match value with
       | Fun (arg, _, body_fun) ->
           let rec_env = Env.add name (VClos { name = Some name; arg; body = body_fun; env }) env in
           eval_expr rec_env body
       | _ -> raise RecWithoutArg )
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