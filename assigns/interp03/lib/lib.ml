
open Utils
include My_parser

let unify _ _ = assert false

let rec type_of (env : stc_env) (expr : expr) : ty_scheme option =
  match expr with
  | Int _ -> Some (Forall ([], TInt))  
  | Float _ -> Some (Forall ([], TFloat))  
  | True | False -> Some (Forall ([], TBool))  
  | Var x -> 
      (try Some (Env.find x env) 
        with Not_found -> None)
  | Fun (arg, _, body) ->
      let arg_ty = TVar (gensym ()) in
      let new_env = Env.add arg (Forall ([], arg_ty)) env in
      (match type_of new_env body with
        | Some (Forall (qs, body_ty)) -> Some (Forall (qs, TFun (arg_ty, body_ty)))
        | None -> None)
  | App (f, arg) ->
      (match (type_of env f, type_of env arg) with
        | Some (Forall (_, TFun (param_ty, ret_ty))), Some (Forall (_, arg_ty)) ->
            if param_ty = arg_ty then Some (Forall ([], ret_ty)) else None
        | _ -> None)
  | Let { is_rec = _is_rec; name; value; body } ->
      (match type_of env value with
        | Some scheme ->
            let new_env = Env.add name scheme env in
            type_of new_env body
        | None -> None)
  | If (cond, then_branch, else_branch) ->
      (match type_of env cond, type_of env then_branch, type_of env else_branch with
        | Some (Forall (_, TBool)), Some (Forall (_, ty1)), Some (Forall (_, ty2)) when ty1 = ty2 ->
            Some (Forall ([], ty1))
        | _ -> None)
  | _ -> None
  

exception AssertFail
exception DivByZero
exception RecWithoutArg
exception CompareFunVals

let eval_expr _ _ = assert false

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
