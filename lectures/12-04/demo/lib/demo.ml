include Utils

let parse (s : string) : prog option =
  match Parser.prog Lexer.read (Lexing.from_string s) with
  | e -> Some e
  | exception _ -> None

type constr = ty * ty
type solution = (string * ty) list

let free_vars =
  let open VarSet in
  let rec go = function
    | TInt | TBool -> empty
    | TVar a -> singleton a
    | TFun (t1, t2) -> union (go t1) (go t2)
  in go

let ty_subst t a =
  let rec go = function
  | TInt -> TInt
  | TBool -> TBool
  | TFun (t1, t2) -> TFun (go t1, go t2)
  | TVar b -> if a = b then t else TVar b
  in go

let unify (cs : constr list) : solution option =
  let rec unify s = function
    | [] -> Some (List.rev s)
    | c :: cs ->
      match c with
      | t1, t2 when t1 = t2 -> unify s cs
      | TFun (s1, t1), TFun (s2, t2) ->
        unify s ((s1, s2) :: (t1, t2) :: cs)
      | TVar a, t when not (VarSet.mem a (free_vars t)) ->
        unify
          ((a, t) :: s)
          (List.map
             (fun (t1, t2) ->
                ty_subst t a t1,
                ty_subst t a t2
             )
             cs)
      | t, TVar a -> unify s ((TVar a, t) :: cs)
      | _ -> None
  in
  unify [] cs

type stc_env = ty_scheme Env.t

let add x t = Env.add x (Forall (VarSet.empty, t))

let count = ref 0

let fresh () =
  count := !count + 1;
  "$" ^ string_of_int !count

let instantiate (Forall (vars, ty)) =
  VarSet.fold
    (fun a ty -> ty_subst (TVar (fresh ())) a ty)
    vars
    ty

let rec type_of (ctxt : stc_env) (e : expr) : ty * constr list =
  match e with
  | Num _ -> TInt, []
  | Add (e1, e2) ->
     (* Γ ⊢ e₁ : τ₁ ⊣ 𝒞₁ *)
     let t1, c1 = type_of ctxt e1 in
     (* Γ ⊢ e₂ : τ₂ ⊣ 𝒞₂ *)
     let t2, c2 = type_of ctxt e2 in
     (* Γ ⊢ e₁ + e₂ : int ⊣ τ₁ ≐ int, τ₂ ≐ int, 𝒞₁, 𝒞₂ *)
     TInt, (t1, TInt) :: (t2, TInt) :: c1 @ c2
  | Eq (e1, e2) ->
     (* Γ ⊢ e₁ : τ₁ ⊣ 𝒞₁ *)
     let t1, c1 = type_of ctxt e1 in
     (* Γ ⊢ e₂ : τ₂ ⊣ 𝒞₂ *)
     let t2, c2 = type_of ctxt e2 in
     (* Γ ⊢ e₁ = e₂ : int ⊣ τ₁ ≐ τ₂ , 𝒞₁, 𝒞₂ *)
     TBool, (t1, t2) :: c1 @ c2
  | If (e1, e2, e3) ->
     let t1, c1 = type_of ctxt e1 in
     let t2, c2 = type_of ctxt e2 in
     let t3, c3 = type_of ctxt e3 in
     t3, (t1, TBool) :: (t2, t3) :: c1 @ c2 @ c3
  | Let (x, e1, e2) ->
     let t1, c1 = type_of ctxt e1 in
     let ctxt = add x t1 ctxt in
     let t2, c2 = type_of ctxt e2 in
     t2, c1 @ c2
  | Fun (x, e) ->
     let a = fresh () in
     let ctxt = add x (TVar a) ctxt in
     let t, c = type_of ctxt e in
     TFun (TVar a, t), c
  | App (e1, e2) ->
     let t1, c1 = type_of ctxt e1 in
     let t2, c2 = type_of ctxt e2 in
     let a = fresh () in
     TVar a, (t1, TFun (t2, TVar a)) :: c1 @ c2
  | Var x ->
     match Env.find_opt x ctxt with
     | None -> TInt, [TInt, TBool]
     | Some tys -> instantiate tys, []

let principal sol ty : ty_scheme =
  let base_ty =
    List.fold_left
      (fun t1 (x, t2) -> ty_subst t2 x t1)
      ty
      sol
  in
  Forall (free_vars base_ty, base_ty)

let is_well_typed (p : prog) : bool =
  let rec go ctxt = function
  | [] -> true
  | (x, e) :: p ->
     (* 1. Constraint-based inference *)
     let t, cnstrs = type_of ctxt e in
     (* 2. Unification *)
     let s_opt = unify cnstrs in
     match s_opt with
     | None -> false
     | Some sol ->
        (* 3. Principal type *)
        let t = principal sol t in
        let _ = print_endline (string_of_ty_scheme t) in
        (* 4. Add to context and continue *)
        let ctxt = Env.add x t ctxt in
        go ctxt p
  in go Env.empty p

let rec eval (env : dyn_env) (e : expr) : value =
  let rec go e =
    let go_int e = match go e with | VNum n -> n | _ -> assert false in
    let go_bool e = match go e with | VBool b -> b | _ -> assert false in
    match e with
    | Let(x, e1, e2) -> eval (Env.add x (go e1) env) e2
    | App (e1, e2) -> (
        match go e1 with
        | VClos (x, e, env') -> eval (Env.add x (go e2) env') e
        | _ -> assert false
      )
    | Var x -> Env.find x env
    | Num n -> VNum n
    | Fun (x, e) -> VClos (x, e, env)
    | Add (e1, e2) -> VNum (go_int e1 + go_int e2)
    | Eq (e1, e2) -> VBool (go_int e1 = go_int e2)
    | If (e1, e2, e3) -> if go_bool e1 then go e2 else go e3
  in go e

let rec desugar = function
  | [] -> assert false
  | (name, binding) :: [] -> Let (name, binding, Var name)
  | (name, binding) :: p ->
    Let (name, binding, desugar p)

let interp (s : string) : value option =
  match parse s with
  | Some p ->
    if is_well_typed p
    then Some (eval Env.empty (desugar p))
    else None
  | None -> None
