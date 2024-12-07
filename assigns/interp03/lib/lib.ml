
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

  (* let rec string_of_ty = function
  | TUnit -> "TUnit"
  | TInt -> "TInt"
  | TFloat -> "TFloat"
  | TBool -> "TBool"
  | TVar x -> "TVar(" ^ x ^ ")"
  | TList t -> "TList(" ^ string_of_ty t ^ ")"
  | TOption t -> "TOption(" ^ string_of_ty t ^ ")"
  | TPair (t1, t2) -> "TPair(" ^ string_of_ty t1 ^ ", " ^ string_of_ty t2 ^ ")"
  | TFun (t1, t2) -> "TFun(" ^ string_of_ty t1 ^ " -> " ^ string_of_ty t2 ^ ")" *)

(* let string_of_constraints constraints =
  "[" ^ String.concat "; " (List.map (fun (t1, t2) -> string_of_ty t1 ^ " = " ^ string_of_ty t2) constraints) ^ "]" *)
  let instantiate (vars, ty) =
    let subst = List.map (fun var -> (var, TVar (gensym ()))) vars in
    apply_subst subst ty
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
let type_of (env : stc_env) (e : expr) : ty_scheme option =
  let rec infer env = function
    | Unit -> (TUnit, [])
    | True | False -> (TBool, [])
    | Int _ -> (TInt, [])
    | Float _ -> (TFloat, [])
    | Var x -> (
        match Env.find_opt x env with
        | Some (Forall (vars, t)) -> (instantiate (vars, t), [])
        | None -> failwith ("Unbound variable: " ^ x)
      )
    | ENone -> (TOption (TVar (gensym ())), [])
    | ESome e ->
      let t, c = infer env e in
      (TOption t, c)
    | Nil -> (TList (TVar (gensym ())), [])
    | OptMatch { matched; some_name; some_case; none_case } ->
      let t_matched, c_matched = infer env matched in
      let fresh = TVar (gensym ()) in
      let env_some = Env.add some_name (Forall ([], fresh)) env in
      let t_some_case, c_some = infer env_some some_case in
      let t_none_case, c_none = infer env none_case in
      let c = (t_matched, TOption fresh) :: (t_some_case, t_none_case) :: c_matched @ c_some @ c_none in
      (t_some_case, c)
    | Bop (op, e1, e2) -> (
        let t1, c1 = infer env e1 in
        let t2, c2 = infer env e2 in
        match op with
        | Add | Sub | Mul | Div | Mod ->
            (TInt, (t1, TInt) :: (t2, TInt) :: c1 @ c2)
        | AddF | SubF | MulF | DivF | PowF ->
            (TFloat, (t1, TFloat) :: (t2, TFloat) :: c1 @ c2)
        | And | Or ->
            (TBool, (t1, TBool) :: (t2, TBool) :: c1 @ c2)
        | Eq | Neq | Lt | Lte | Gt | Gte ->
            let fresh = TVar (gensym ()) in
            (TBool, (t1, fresh) :: (t2, fresh) :: c1 @ c2)
        | Cons ->
          let fresh = TVar (gensym ()) in
          (TList fresh, (t1, fresh) :: (t2, TList fresh) :: c1 @ c2)
        | Concat ->
          let fresh = TVar (gensym ()) in
          (TList fresh, (t1, TList fresh) :: (t2, TList fresh) :: c1 @ c2)
        | Comma ->
          (TPair (t1, t2), c1 @ c2)
      )
    | If (e1, e2, e3) ->
        let t1, c1 = infer env e1 in
        let t2, c2 = infer env e2 in
        let t3, c3 = infer env e3 in
        (t2, (t1, TBool) :: (t2, t3) :: c1 @ c2 @ c3)
    | Fun (x, Some ty, body) ->
        let env = Env.add x (Forall ([], ty)) env in 
        let t_body, c_body = infer env body in
        (TFun (ty, t_body), c_body)
    | Fun (x, None, body) ->
        let fresh = TVar (gensym ()) in
        let env = Env.add x (Forall ([], fresh)) env in
        let t_body, c_body = infer env body in
        (TFun (fresh, t_body), c_body)
    | App (e1, e2) ->
        let t_fun, c_fun = infer env e1 in
        let t_arg, c_arg = infer env e2 in
        let fresh = TVar (gensym ()) in
        (fresh, (t_fun, TFun (t_arg, fresh)) :: c_fun @ c_arg)
    | Let { name; value; body; _} ->
        let t_val, c_val = infer env value in
        let free_in_env =
          List.concat (List.map (fun (_, Forall (_, t)) -> free_vars t) (Env.to_list env)) in
        let free_in_t_val = free_vars t_val in
        let generalized = List.filter (fun v -> not (List.mem v free_in_env)) free_in_t_val in
        let generalized_ty = Forall (generalized, t_val) in
        let env = Env.add name generalized_ty env in
        let t_body, c_body = infer env body in
        (t_body, c_val @ c_body)
    | PairMatch { matched; fst_name; snd_name; case } ->
      let t_matched, c_matched = infer env matched in
      let fresh1 = TVar (gensym ()) in
      let fresh2 = TVar (gensym ()) in
      let extended_env = Env.add fst_name (Forall ([], fresh1)) (Env.add snd_name (Forall ([], fresh2)) env) in
      let t_case, c_case = infer extended_env case in
      (t_case, (t_matched, TPair (fresh1, fresh2)) :: c_matched @ c_case)
    | ListMatch { matched; hd_name; tl_name; cons_case; nil_case } ->
        let t_matched, c_matched = infer env matched in
        let fresh = TVar (gensym ()) in
        let extended_env = 
          Env.add hd_name (Forall ([], fresh)) 
            (Env.add tl_name (Forall ([], TList fresh)) env)
        in
        let t_cons_case, c_cons_case = infer extended_env cons_case in
        let t_nil_case, c_nil_case = infer env nil_case in
        (t_nil_case, 
          (t_matched, TList fresh) :: (t_cons_case, t_nil_case) :: 
          c_matched @ c_cons_case @ c_nil_case)
    | Assert e ->
        let t, c = infer env e in
        (TUnit, (t, TBool) :: c)
    | Annot (e, ty) ->
        let t, c = infer env e in
        (ty, (t, ty) :: c)
  in
  try
    let t, c = infer env e in
    match unify t c with
    | Some (Forall (vars, ty)) -> Some (Forall (vars, ty))
    | None -> None
  with _ -> None



exception AssertFail
exception DivByZero
exception RecWithoutArg
exception CompareFunVals

let rec eval_expr env expr : value =
  let rec go = function
  | Unit -> VUnit
  | True -> VBool true
  | False -> VBool false
  | Int n -> VInt n
  | Float f -> VFloat f
  | ENone -> VNone
  | Nil -> VList []
  | Var x -> (
      try Env.find x env
      with Not_found -> failwith "Undefined variable"
    )
  | Fun (x, _, body) -> VClos { name = None; arg = x; body; env }
  | App (e1, e2) -> (
      match go e1 with
      | VClos { env; name; arg; body } ->
          let env =
            match name with
            | None -> env
            | Some name -> Env.add name (VClos { env; name = Some name; arg; body }) env
          in
          let env = Env.add arg (go e2) env in
          eval_expr env body
      | _ -> failwith "impossible"
    )
  | Bop (Add, e1, e2) -> (
      match go e1, go e2 with
      | VInt m, VInt n -> VInt (m + n)
      | _ -> failwith "impossible"
    )
  | Bop (AddF, e1, e2) -> (
      match go e1, go e2 with
      | VFloat m, VFloat n -> VFloat (m +. n)
      | _ -> failwith "impossible"
    )
  | Bop (Sub, e1, e2) -> (
      match go e1, go e2 with
      | VInt m, VInt n -> VInt (m - n)
      | _ -> failwith "impossible"
    )
  | Bop (SubF, e1, e2) -> (
      match go e1, go e2 with
      | VFloat m, VFloat n -> VFloat (m -. n)
      | _ -> failwith "impossible"
    )
  | Bop (Mul, e1, e2) -> (
      match go e1, go e2 with
      | VInt m, VInt n -> VInt (m * n)
      | _ -> failwith "impossible"
    )
  | Bop (MulF, e1, e2) -> (
      match go e1, go e2 with
      | VFloat m, VFloat n -> VFloat (m *. n)
      | _ -> failwith "impossible"
    )
  | Bop (Div, e1, e2) -> (
      match go e1, go e2 with
      | VInt _, VInt 0 -> raise DivByZero
      | VInt m, VInt n -> VInt (m / n)
      | _ -> failwith "impossible"
    )
  | Bop (DivF, e1, e2) -> (
      match go e1, go e2 with
      | VFloat m, VFloat n when n <> 0.0 -> VFloat (m /. n)
      | _ -> failwith "impossible"
    )
  | Bop (Mod, e1, e2) -> (
      match go e1, go e2 with
      | VInt m, VInt n when n <> 0 -> VInt (m mod n)
      | VInt _, VInt 0 -> failwith "Division by zero in modulo operation"
      | _ -> failwith "Modulo operation requires two numbers"
    )
  | Bop (PowF, e1, e2) -> (
      match go e1, go e2 with
      | VFloat m, VFloat n -> VFloat (m ** n)
      | _ -> failwith "impossible"
    )
  | Bop (Eq, e1, e2) -> (
      match go e1, go e2 with
      | VClos _, _ | _, VClos _ -> raise CompareFunVals
      | VInt m, VInt n -> VBool (m = n)
      | VFloat m, VFloat n -> VBool (m = n)
      | _ -> failwith "must be 2 of same numerical type"
    )
  | Bop (Neq, e1, e2) -> (
      match go e1, go e2 with
      | VClos _, _ | _, VClos _ -> raise CompareFunVals
      | VInt m, VInt n -> VBool (m <> n)
      | VFloat m, VFloat n -> VBool (m <> n)
      | _ -> failwith "must be 2 of same numerical type"
    )
  | Bop (Lt, e1, e2) -> (
      match go e1, go e2 with
      | VInt m, VInt n -> VBool (m < n)
      | VFloat m, VFloat n -> VBool (m < n)
      | _ -> failwith "must be 2 of same numerical type"
    )
  | Bop (Lte, e1, e2) -> (
      match go e1, go e2 with
      | VInt m, VInt n -> VBool (m <= n)
      | VFloat m, VFloat n -> VBool (m <= n)
      | _ -> failwith "must be 2 of same numerical type"
    )
  | Bop (Gt, e1, e2) -> (
      match go e1, go e2 with
      | VInt m, VInt n -> VBool (m > n)
      | VFloat m, VFloat n -> VBool (m > n)
      | _ -> failwith "must be 2 of same numerical type"
    )
  | Bop (Gte, e1, e2) -> (
      match go e1, go e2 with
      | VInt m, VInt n -> VBool (m >= n)
      | VFloat m, VFloat n -> VBool (m >= n)
      | _ -> failwith "must be 2 of same numerical type"
    )
  | Bop (And, e1, e2) -> (
      match go e1 with
      | VBool false -> VBool false
      | VBool true -> go e2
      | _ -> failwith "Logical 'and' requires boolean operands"
    )
  | Bop (Or, e1, e2) -> (
      match go e1 with
      | VBool true -> VBool true
      | VBool false -> go e2
      | _ -> failwith "Logical 'or' requires boolean operands"
    )
  | Bop (Comma, e1, e2) -> VPair (go e1, go e2)
  | Bop (Concat, e1, e2) -> (
      match go e1, go e2 with
      | VList lst1, VList lst2 -> VList (lst1 @ lst2)
      | _ -> failwith "Both operands of Concat must be lists"
    )
  | Bop (Cons, e1, e2) -> (
      match go e2 with
      | VList lst -> VList (go e1 :: lst)
      | _ -> failwith "Expected a list on the right-hand side of Cons"
    )
  | If (e1, e2, e3) -> (
      match go e1 with
      | VBool true -> go e2
      | VBool false -> go e3
      | _ -> failwith "Condition in if-expression must be a boolean"
    )
  | ESome e -> VSome (go e)
  | OptMatch { matched; some_name; some_case; none_case } -> (
      match go matched with
      | VSome v -> eval_expr (Env.add some_name v env) some_case
      | VNone -> eval_expr env none_case
      | _ -> failwith "Expected an option"
    )
  | ListMatch { matched; hd_name; tl_name; cons_case; nil_case } -> (
      match go matched with
      | VList (vh :: vt) ->
          let env = Env.add hd_name vh (Env.add tl_name (VList vt) env) in
          eval_expr env cons_case
      | VList [] -> eval_expr env nil_case
      | _ -> failwith "Expected a list"
    )
  | PairMatch { matched; fst_name; snd_name; case } -> (
      match go matched with
      | VPair (v1, v2) ->
          let env = Env.add fst_name v1 (Env.add snd_name v2 env) in
          eval_expr env case
      | _ -> failwith "Expected a pair"
    )
  | Let { is_rec = false; name; value; body } ->
      let v1 = go value in
      eval_expr (Env.add name v1 env) body
  | Let { is_rec = true; name = f; value = e1; body = e2 } -> (
      match eval_expr env e1 with
      | VClos { name = None; arg; body = closure_body; env = closure_env } ->
          let closure = VClos { name = Some f; arg; body = closure_body; env = closure_env } in
          eval_expr (Env.add f closure env) e2
      | _ -> failwith "Expected a closure in recursive let binding"
    )
  | Annot (e, _) -> go e
  | Assert e1 -> (
      match go e1 with
      | VBool true -> VUnit
      | VBool false -> raise AssertFail
      | _ -> raise AssertFail
    )
  in
  go expr



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