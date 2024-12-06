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

  let rec string_of_ty = function
  | TUnit -> "TUnit"
  | TInt -> "TInt"
  | TFloat -> "TFloat"
  | TBool -> "TBool"
  | TVar x -> "TVar(" ^ x ^ ")"
  | TList t -> "TList(" ^ string_of_ty t ^ ")"
  | TOption t -> "TOption(" ^ string_of_ty t ^ ")"
  | TPair (t1, t2) -> "TPair(" ^ string_of_ty t1 ^ ", " ^ string_of_ty t2 ^ ")"
  | TFun (t1, t2) -> "TFun(" ^ string_of_ty t1 ^ " -> " ^ string_of_ty t2 ^ ")"

(* let string_of_constraints constraints =
  "[" ^ String.concat "; " (List.map (fun (t1, t2) -> string_of_ty t1 ^ " = " ^ string_of_ty t2) constraints) ^ "]" *)

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
let rec type_of' (ctxt: stc_env) (e: expr) : ty * (ty * ty) list =
  let rec go e =
    match e with
    | Unit ->
      let _ = print_endline "Matched Unit" in
      TUnit, []
    | True | False ->
      let _ = print_endline "Matched True/False" in
      TBool, []
    | Int _ ->
      let _ = print_endline "Matched Int" in
      TInt, []
    | Float _ ->
      let _ = print_endline "Matched Float" in
      TFloat, []
    | Var x ->
      let _ = print_endline ("Matched Var: " ^ x) in
      let Forall (bnd_vars, t) = Env.find x ctxt in
      let rec instantiate bnd_vars t =
        match bnd_vars with
        | [] -> t
        | v :: vs -> instantiate vs (apply_subst [(v, TVar (gensym ()))] t)
      in
      instantiate bnd_vars t, []
    | Annot (e, ty) ->
      let _ = print_endline "Matched Annot" in
      let inferred_ty, constraints = go e in
      ty, (inferred_ty, ty) :: constraints
    | Let { is_rec = false; name; value; body } ->
      let _ = print_endline ("Matched Let: " ^ name) in
      let value_ty, value_constraints = go value in
      let body_ty, body_constraints = type_of' (Env.add name (Forall ([], value_ty)) ctxt) body in
      body_ty, value_constraints @ body_constraints
    | Let { is_rec = true; name; value; body } ->
      let _ = print_endline ("Matched Recursive Let: " ^ name) in
      (match value with
       | Fun (arg, _, body_fun) ->
         let arg_ty = TVar (gensym ()) in
         let ret_ty = TVar (gensym ()) in
         let fun_ty = TFun (arg_ty, ret_ty) in
         let body_fun_ty, body_fun_constraints =
           type_of' (Env.add arg (Forall ([], arg_ty)) (Env.add name (Forall ([], fun_ty)) ctxt)) body_fun
         in
         let constraints = (ret_ty, body_fun_ty) :: body_fun_constraints in
         let body_ty, body_constraints = type_of' (Env.add name (Forall ([], fun_ty)) ctxt) body in
         body_ty, constraints @ body_constraints
       | _ -> failwith "Recursive let must bind to a function")
    | Fun (arg, ty_opt, body) ->
      let _ = print_endline ("Matched Fun: " ^ arg) in
      let arg_ty = match ty_opt with Some ty -> ty | None -> TVar (gensym ()) in
      let body_ty, body_constraints = go body in
      TFun (arg_ty, body_ty), body_constraints
    | App (f, arg) ->
      let _ = print_endline "Matched App" in
      let param_ty = TVar (gensym ()) in
      let return_ty = TVar (gensym ()) in
      let func_ty, func_constraints = go f in
      let arg_ty, arg_constraints = go arg in
      return_ty, (func_ty, TFun (param_ty, return_ty)) :: (arg_ty, param_ty) :: func_constraints @ arg_constraints
    | Bop (Comma, e1, e2) ->
      let _ = print_endline "Matched Pair (Bop Comma)" in
      let t1, c1 = go e1 in
      let t2, c2 = go e2 in
      TPair (t1, t2), c1 @ c2
    | PairMatch { matched; fst_name; snd_name; case } ->
      let _ = print_endline "Matched PairMatch" in
      let fst_ty = TVar (gensym ()) in
      let snd_ty = TVar (gensym ()) in
      let pair_ty = TPair (fst_ty, snd_ty) in
      let matched_ty, matched_constraints = go matched in
      let case_ty, case_constraints =
        type_of' (Env.add fst_name (Forall ([], fst_ty)) (Env.add snd_name (Forall ([], snd_ty)) ctxt)) case
      in
      case_ty, (matched_ty, pair_ty) :: matched_constraints @ case_constraints
    | _ -> failwith "Expression not supported in type_of'"
  in
  go e

(* type_of: Uses type_of' to compute the type and unify constraints *)
let type_of ctxt e =
  let t, c = type_of' ctxt e in
  let _ =
    print_endline ("Inferred type: " ^ string_of_ty t);
    print_endline ("Constraints: " ^
      String.concat ", " (List.map (fun (t1, t2) -> string_of_ty t1 ^ " = " ^ string_of_ty t2) c))
  in
  let t' = unify t (c @ [(TVar "$_out", t)]) in
  match t' with
  | None ->
    let _ = print_endline "Unification failed" in
    None
  | Some (Forall (vars, t')) ->
    let _ = print_endline ("Unified type: " ^ string_of_ty t') in
    Some (Forall (vars, t'))

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