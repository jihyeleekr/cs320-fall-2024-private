open Utils

(* Parse function *)
let parse = My_parser.parse

(* Exceptions for runtime errors *)
exception DivByZero
exception AssertFail

(* Desugaring: Convert prog to expr *)
let desugar (prog : prog) : expr =
    let rec desugar_toplets = function
      | [] -> Unit 
      | { is_rec; name; args; ty; value } :: rest ->
          let desugared_value =
            List.fold_right
              (fun (arg, arg_ty) acc -> Fun (arg, arg_ty, acc))
              args
              (desugar_expr value)
          in
          Let {
            is_rec;
            name;
            ty;
            value = desugared_value;
            body = desugar_toplets rest;
          }
    and desugar_expr = function
      | SLet { is_rec; name; args; ty; value; body } ->
          let desugared_value =
            List.fold_right
              (fun (arg, arg_ty) acc -> Fun (arg, arg_ty, acc))
              args
              (desugar_expr value)
          in
          Let {
            is_rec;
            name;
            ty;
            value = desugared_value;
            body = desugar_expr body;
          }
      | SFun { arg; args; body } ->
          List.fold_right
            (fun (arg, arg_ty) acc -> Fun (arg, arg_ty, acc))
            (arg :: args)
            (desugar_expr body)
      | SIf (cond, then_, else_) ->
          If (desugar_expr cond, desugar_expr then_, desugar_expr else_)
      | SApp (e1, e2) ->
          App (desugar_expr e1, desugar_expr e2)
      | SBop (op, e1, e2) ->
          Bop (op, desugar_expr e1, desugar_expr e2)
      | SAssert e ->
          Assert (desugar_expr e)
      | SUnit -> Unit
      | STrue -> True
      | SFalse -> False
      | SNum n -> Num n
      | SVar x -> Var x
    in
    desugar_toplets prog
  
(* Type checking *)
let type_of (expr : expr) : (ty, error) result =
    let rec typecheck env expr =
      match expr with
      | Unit -> Ok UnitTy
      | Num _ -> Ok IntTy
      | True | False -> Ok BoolTy  
      | Var x -> (
          match Env.find_opt x env with
          | Some ty -> Ok ty
          | None -> Error (UnknownVar x)
        )  
      | Let { is_rec; name; ty = expected_ty; value; body } -> (
          match typecheck env value with
          | Ok actual_ty ->
              if actual_ty = expected_ty then
                let extended_env =
                  if is_rec then Env.add name expected_ty env else env
                in
                typecheck (Env.add name expected_ty extended_env) body
              else
                Error (LetTyErr (expected_ty, actual_ty))
          | Error e -> Error e
        )  
      | Fun (arg, arg_ty, body) ->
          let extended_env = Env.add arg arg_ty env in
          (match typecheck extended_env body with
          | Ok body_ty -> Ok (FunTy (arg_ty, body_ty))
          | Error e -> Error e)  
      | App (e1, e2) -> (
          match typecheck env e1, typecheck env e2 with
          | Ok (FunTy (arg_ty, ret_ty)), Ok actual_ty ->
              if arg_ty = actual_ty then Ok ret_ty
              else Error (FunArgTyErr (arg_ty, actual_ty))
          | Ok ty, _ -> Error (FunAppTyErr ty)
          | Error e, _ -> Error e
        )  
      | If (cond, then_, else_) -> (
          match typecheck env cond with
          | Ok BoolTy -> (
              match typecheck env then_, typecheck env else_ with
              | Ok ty_then, Ok ty_else when ty_then = ty_else -> Ok ty_then
              | Ok ty_then, Ok ty_else -> Error (IfTyErr (ty_then, ty_else))
              | Error e, _ | _, Error e -> Error e
            )
          | Ok ty -> Error (IfCondTyErr ty)
          | Error e -> Error e
        )  
      | Bop (op, e1, e2) -> (
          match typecheck env e1, typecheck env e2 with
          | Ok IntTy, Ok IntTy when List.mem op [Add; Sub; Mul; Div; Mod] -> Ok IntTy
          | Ok IntTy, Ok IntTy when List.mem op [Lt; Lte; Gt; Gte; Eq; Neq] -> Ok BoolTy
          | Ok BoolTy, Ok BoolTy when List.mem op [And; Or] -> Ok BoolTy
          | Error e, _ -> Error e
          | _, Error e -> Error e
          | Ok ty1, _ when List.mem op [Add; Sub; Mul; Div; Mod] -> Error (OpTyErrL (op, IntTy, ty1))
          | Ok ty1, _ when List.mem op [Lt; Lte; Gt; Gte; Eq; Neq] -> Error (OpTyErrL (op, IntTy, ty1))
          | Ok ty1, _ when List.mem op [And; Or] -> Error (OpTyErrL (op, BoolTy, ty1))
          | _, Ok ty2 when List.mem op [Add; Sub; Mul; Div; Mod] -> Error (OpTyErrR (op, IntTy, ty2))
          | _, Ok ty2 when List.mem op [Lt; Lte; Gt; Gte; Eq; Neq] -> Error (OpTyErrR (op, IntTy, ty2))
          | _, Ok ty2 when List.mem op [And; Or] -> Error (OpTyErrR (op, BoolTy, ty2))
          | Ok ty1, Ok ty2 -> Error (OpTyErrL (op, ty1, ty2))
        )
    | Assert e -> (
        match typecheck env e with
        | Ok BoolTy -> Ok UnitTy
        | Ok ty -> Error (AssertTyErr ty)
        | Error e -> Error e
    )
    in
    typecheck Env.empty expr
  

(* Evaluation *)
let eval (expr : expr) : value =
  let rec eval_expr env expr =
    match expr with
    | Unit -> VUnit
    | Num n -> VNum n
    | True -> VBool true
    | False -> VBool false
    | Var x -> Env.find x env
    | Let { is_rec; name; ty = _ty; value; body } -> 
        let closure_env =
          if is_rec then
            Env.add name (VClos { name = Some name; arg = ""; body = value; env }) env
          else env
        in
        let v = eval_expr closure_env value in
        let new_env = Env.add name v closure_env in
        eval_expr new_env body
    | Fun (arg, _, body) -> VClos { name = None; arg; body; env }
    | App (e1, e2) -> (
        match eval_expr env e1 with
        | VClos { name = _name; arg; body; env = env' } -> 
            let v = eval_expr env e2 in
            let extended_env = Env.add arg v env' in
            eval_expr extended_env body
        | _ -> assert false)
    | If (cond, then_, else_) ->
        let cond_val = eval_expr env cond in
        if cond_val = VBool true then eval_expr env then_ else eval_expr env else_
    | Bop (op, e1, e2) -> (
        let v1 = eval_expr env e1 in
        let v2 = eval_expr env e2 in
        match (v1, v2, op) with
        | VNum n1, VNum n2, Add -> VNum (n1 + n2)
        | VNum n1, VNum n2, Sub -> VNum (n1 - n2)
        | VNum n1, VNum n2, Mul -> VNum (n1 * n2)
        | VNum n1, VNum n2, Div ->
            if n2 = 0 then raise DivByZero else VNum (n1 / n2)
        | VNum n1, VNum n2, Mod -> VNum (n1 mod n2)
        | VNum n1, VNum n2, Lt -> VBool (n1 < n2)
        | VNum n1, VNum n2, Lte -> VBool (n1 <= n2)
        | VNum n1, VNum n2, Gt -> VBool (n1 > n2)
        | VNum n1, VNum n2, Gte -> VBool (n1 >= n2)
        | VNum n1, VNum n2, Eq -> VBool (n1 = n2)
        | VNum n1, VNum n2, Neq -> VBool (n1 <> n2)
        | VBool b1, VBool b2, And -> VBool (b1 && b2)
        | VBool b1, VBool b2, Or -> VBool (b1 || b2)
        | _ -> assert false)
    | Assert e ->
        let v = eval_expr env e in
        if v = VBool true then VUnit else raise AssertFail
  in
  eval_expr Env.empty expr

  let interp (input : string) : (value, error) result =
    match parse input with
    | Some prog -> (
        let expr = desugar prog in
        match type_of expr with
        | Ok _ -> Ok (eval expr)
        | Error e -> Error e
    )
    | None -> Error ParseErr