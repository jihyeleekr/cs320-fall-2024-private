open Utils
include My_parser

(* Helper Functions *)
let rec occurs x ty =
  match ty with
  | TVar y -> x = y
  | TFun (t1, t2) | TPair (t1, t2) -> occurs x t1 || occurs x t2
  | TList t | TOption t -> occurs x t
  | _ -> false

let rec free_vars ty =
  match ty with
  | TVar x -> [x]
  | TFun (t1, t2) | TPair (t1, t2) -> free_vars t1 @ free_vars t2
  | TList t | TOption t -> free_vars t
  | _ -> []

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

(* Custom sort_uniq function *)
let sort_uniq cmp lst =
  let sorted = List.sort cmp lst in
  let rec uniq acc = function
    | [] -> List.rev acc
    | [x] -> List.rev (x :: acc)
    | x :: (y :: _ as rest) -> if cmp x y = 0 then uniq acc rest else uniq (x :: acc) rest
  in
  uniq [] sorted

(* Unify Function *)
let rec unify ty constraints =
  match constraints with
  | [] -> 
    let free = sort_uniq compare (free_vars ty) in
    Some (Forall (free, ty)) 
  | (t1, t2) :: rest when t1 = t2 -> unify ty rest 
  | (TVar x, t) :: rest | (t, TVar x) :: rest ->
    if occurs x t then None 
    else
      let subst = [(x, t)] in
      let unified_ty = apply_subst subst ty in
      let unified_constraints = apply_subst_to_constraints subst rest in
      (match unify unified_ty unified_constraints with
       | Some (Forall (vars, final_ty)) ->
         let new_vars = List.filter (fun v -> v <> x) vars in
         Some (Forall (new_vars, final_ty))
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

  | Annot (e, ty) ->
    (match type_of env e with
     | Some (Forall (_, inferred_ty)) ->
       let constraints = [(inferred_ty, ty)] in
       (match unify ty constraints with
        | Some (Forall (_, unified_ty)) -> Some (Forall ([], unified_ty))
        | None -> None)
     | None -> None)

  | Let { is_rec = false; name; value; body } ->
  (match type_of env value with
    | Some inferred_scheme -> 
        let env' = Env.add name inferred_scheme env in
        type_of env' body
    | None -> None)
    

  | Let { is_rec = true; name; value; body } ->
    (match value with
     | Fun (arg, _, body_fun) ->
       let arg_ty = TVar (gensym ()) in
       let ret_ty = TVar (gensym ()) in
       let fun_ty = TFun (arg_ty, ret_ty) in
       let env' = Env.add name (Forall ([], fun_ty)) env in
       (match type_of (Env.add arg (Forall ([], arg_ty)) env') body_fun with
        | Some (Forall (_, inferred_ret_ty)) ->
          let constraints = [(ret_ty, inferred_ret_ty)] in
          (match unify fun_ty constraints with
           | Some (Forall (_, unified_fun_ty)) ->
             type_of (Env.add name (Forall ([], unified_fun_ty)) env) body
           | None -> None)
        | None -> None)
     | _ -> None)

  | Fun (arg, ty_opt, body) ->
    let arg_ty = match ty_opt with Some ty -> ty | None -> TVar (gensym ()) in
    let env' = Env.add arg (Forall ([], arg_ty)) env in
    (match type_of env' body with
     | Some (Forall (_, body_ty)) -> Some (Forall ([], TFun (arg_ty, body_ty)))
     | _ -> None)

  | App (f, arg) ->
    let param_ty = TVar (gensym ()) in
    let return_ty = TVar (gensym ()) in
    (match type_of env f, type_of env arg with
      | Some (Forall (_, func_ty)), Some (Forall (_, actual_arg_ty)) ->
        let constraints = [(func_ty, TFun (param_ty, return_ty)); (param_ty, actual_arg_ty)] in
        (match unify return_ty constraints with
        | Some (Forall (_, unified_ty)) -> Some (Forall ([], unified_ty))
        | None -> None)
      | _ -> None)
  | If (cond, e1, e2) ->
    (match type_of env cond, type_of env e1, type_of env e2 with
     | Some (Forall (_, TBool)), Some (Forall (_, t1)), Some (Forall (_, t2)) ->
       let constraints = [(t1, t2)] in
       (match unify t1 constraints with
        | Some (Forall (_, unified_ty)) -> Some (Forall ([], unified_ty))
        | None -> None)
     | _ -> None)

  | Bop (op, e1, e2) ->
    let (result_ty, operand_ty) =
      match op with
      | Add | Sub | Mul | Div | Mod -> (TInt, TInt)
      | AddF | SubF | MulF | DivF | PowF -> (TFloat, TFloat)
      | Cons ->
        let elem_ty = TVar (gensym ()) in
        (TList elem_ty, elem_ty)
      | Concat ->
        let list_ty = TList (TVar (gensym ())) in
        (list_ty, list_ty)
      | Comma ->
        let t1 = TVar (gensym ()) in
        let t2 = TVar (gensym ()) in
        (TPair (t1, t2), t1)
      | Lt | Lte | Gt | Gte | Eq | Neq -> (TBool, TVar (gensym ()))
      | And | Or -> (TBool, TBool)
    in
    (match type_of env e1, type_of env e2 with
     | Some (Forall (_, t1)), Some (Forall (_, t2)) ->
       let constraints =
         match op with
         | Cons -> [(t1, operand_ty); (t2, TList operand_ty)]
         | Concat -> [(t1, operand_ty); (t2, operand_ty)]
         | Comma -> []
         | _ -> [(t1, operand_ty); (t2, operand_ty)]
       in
       (match unify result_ty constraints with
        | Some (Forall (_, unified_ty)) -> Some (Forall ([], unified_ty))
        | None -> None)
     | _ -> None)

  | ListMatch { matched; hd_name; tl_name; cons_case; nil_case } ->
    let elem_ty = TVar (gensym ()) in
    let list_ty = TList elem_ty in
    (match type_of env matched,
           type_of (Env.add hd_name (Forall ([], elem_ty))
           (Env.add tl_name (Forall ([], list_ty)) env)) cons_case,
           type_of env nil_case with
     | Some (Forall (_, matched_ty)), Some (Forall (_, cons_ty)), Some (Forall (_, nil_ty)) ->
       let constraints = [(matched_ty, list_ty); (cons_ty, nil_ty)] in
       (match unify cons_ty constraints with
        | Some (Forall (_, unified_ty)) -> Some (Forall ([], unified_ty))
        | None -> None)
     | _ -> None)

  | PairMatch { matched; fst_name; snd_name; case } ->
    let fst_ty = TVar (gensym ()) in
    let snd_ty = TVar (gensym ()) in
    let pair_ty = TPair (fst_ty, snd_ty) in
    (match type_of env matched,
           type_of (Env.add fst_name (Forall ([], fst_ty))
           (Env.add snd_name (Forall ([], snd_ty)) env)) case with
     | Some (Forall (_, matched_ty)), Some (Forall (_, case_ty)) ->
       let constraints = [(matched_ty, pair_ty)] in
       (match unify case_ty constraints with
        | Some (Forall (_, unified_ty)) -> Some (Forall ([], unified_ty))
        | None -> None)
     | _ -> None)

  | OptMatch { matched; some_name; some_case; none_case } ->
    let elem_ty = TVar (gensym ()) in
    let opt_ty = TOption elem_ty in
    (match type_of env matched,
           type_of (Env.add some_name (Forall ([], elem_ty)) env) some_case,
           type_of env none_case with
     | Some (Forall (_, matched_ty)), Some (Forall (_, some_ty)), Some (Forall (_, none_ty)) ->
       let constraints = [(matched_ty, opt_ty); (some_ty, none_ty)] in
       (match unify some_ty constraints with
        | Some (Forall (_, unified_ty)) -> Some (Forall ([], unified_ty))
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
       with Not_found -> raise (Failure ("Undefined variable: " ^ x)))
  | Assert e ->
      (match eval_expr env e with
       | VBool true -> VUnit
       | VBool false -> raise AssertFail
       | _ -> raise (Failure "Assert expects a boolean"))
  | ENone -> VNone
  | ESome e -> VSome (eval_expr env e)
  | OptMatch { matched; some_name; some_case; none_case } ->
      (match eval_expr env matched with
       | VSome v -> eval_expr (Env.add some_name v env) some_case
       | VNone -> eval_expr env none_case
       | _ -> raise (Failure "Option match expects Some or None"))
  | Nil -> VList []
  | Bop (Cons, hd, tl) ->
      (match eval_expr env tl with
       | VList lst -> VList (eval_expr env hd :: lst)
       | _ -> raise (Failure "Cons expects a list"))
  | ListMatch { matched; hd_name; tl_name; cons_case; nil_case } ->
      (match eval_expr env matched with
       | VList (hd :: tl) ->
           let env' = Env.add hd_name hd (Env.add tl_name (VList tl) env) in
           eval_expr env' cons_case
       | VList [] -> eval_expr env nil_case
       | _ -> raise (Failure "List match expects a list"))
  | Bop (Comma, e1, e2) ->
      let v1 = eval_expr env e1 in
      let v2 = eval_expr env e2 in
      VPair (v1, v2)
  | PairMatch { matched; fst_name; snd_name; case } ->
      (match eval_expr env matched with
       | VPair (v1, v2) ->
           let env' = Env.add fst_name v1 (Env.add snd_name v2 env) in
           eval_expr env' case
       | _ -> raise (Failure "Pair match expects a pair"))
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
       | (Lt, VInt n1, VInt n2) -> VBool (n1 < n2)
       | (Lte, VInt n1, VInt n2) -> VBool (n1 <= n2)
       | (Gt, VInt n1, VInt n2) -> VBool (n1 > n2)
       | (Gte, VInt n1, VInt n2) -> VBool (n1 >= n2)
       | (And, VBool b1, VBool b2) -> VBool (b1 && b2)
       | (Or, VBool b1, VBool b2) -> VBool (b1 || b2)
       | _ -> raise (Failure "Unsupported binary operation"))
  | If (cond, then_branch, else_branch) ->
      (match eval_expr env cond with
       | VBool true -> eval_expr env then_branch
       | VBool false -> eval_expr env else_branch
       | _ -> raise (Failure "If condition expects a boolean"))
  | Fun (arg, _, body) -> VClos { name = None; arg; body; env }
  | App (f, arg) ->
      (match eval_expr env f with
       | VClos { name; arg = param; body; env = closure_env } ->
           let arg_val = eval_expr env arg in
           let env' =
             match name with
             | Some name -> Env.add name (VClos { name = Some name; arg = param; body; env = closure_env }) closure_env
             | None -> closure_env
           in
           eval_expr (Env.add param arg_val env') body
       | _ -> raise (Failure "Application expects a function"))
  | Let { is_rec = false; name; value; body } ->
      let value_val = eval_expr env value in
      eval_expr (Env.add name value_val env) body
  | Let { is_rec = true; name; value; body } ->
      (match value with
       | Fun (arg, _, body_fun) ->
           let rec_env = Env.add name (VClos { name = Some name; arg; body = body_fun; env }) env in
           eval_expr rec_env body
       | _ -> raise RecWithoutArg)
  | _ -> raise (Failure "Unsupported expression")


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