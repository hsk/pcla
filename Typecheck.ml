open Claire
open FOL
open Env

let rec union a = function
  | [] -> a
  | (b::bs) when List.mem b a -> union a bs
  | (b::bs) -> union (a@[b]) bs
let unions a = List.fold_left union [] a

type utype = int typeForm
let rec show_utype = show_tf (fun x->string_of_int x)
let show_utypepair (t1,t2) = Printf.sprintf "(%s,%s)" (show_utype t1) (show_utype t2)
let show_utypepairs ts = String.concat "," (List.map show_utypepair ts)

exception UnificationFailed of (utype * utype) (* deriving (Show) *)
exception NotFound of (ident * env) (* deriving (Show) *)

let cnt = ref 0
let reset () = cnt := 0
let new_id () = cnt := !cnt + 1; !cnt

let rec fvT : utype -> int list = function
  | VarT(v) -> [v]
  | ConT(_, ts) -> unions (List.map fvT ts)
  | ArrT(t1, t2) -> union (fvT t1) (fvT t2)
  | Prop -> []
let occurs i t = if List.mem i (fvT t) then raise(UnificationFailed(VarT i, t))

let rec unify s = function
  | x,y when x = y -> s
  | VarT i, t when List.mem_assoc (VarT i) s -> unify s (List.assoc (VarT i) s, t)
  | VarT i, t -> occurs i t; union [VarT i,t] s
  | t, VarT i -> unify s (VarT i, t)
  | ConT(con1, xs), ConT(con2, ys) when con1 = con2 && List.length xs = List.length ys ->
    List.fold_left unify s (List.combine xs ys)
  | ArrT(x1, x2), ArrT(y1, y2) -> unify (unify s (x2, y2)) (x1, y1)
  | x,y -> raise (UnificationFailed(x, y))

let instantiate t : utype =
  let c = ref M.empty in
  let rec f = function
    | VarT(i) when M.mem i !c -> VarT(M.find i !c)
    | VarT(i) -> let n = new_id () in c := M.add i n !c; VarT n
    | Prop -> Prop
    | ArrT(x, y) -> ArrT(f x,f y)
    | ConT(con, xs)-> ConT(con, List.map f xs)
  in
  f t

type ctx = utype M.t
let ctx = ref M.empty
let rec inferTerm env s = function
  | Var v when M.mem v env -> instantiate (M.find v env),s
  | Var v when M.mem v !ctx -> M.find v !ctx,s
  | Var v -> let typ = VarT(new_id()) in ctx := M.add v typ !ctx; typ,s
  | Abs(xs, e) ->
    let xts = List.map (fun x -> (x,VarT(new_id()))) xs in
    ctx := List.fold_left (fun ctx (x,t) -> M.add x t ctx) !ctx xts;
    let t2,s = inferTerm env s e in
    ctx := List.fold_left (fun ctx x -> M.remove x ctx) !ctx xs;
    let t = VarT(new_id()) in
    t,unify s (List.fold_right(fun (_,t) t2 -> ArrT(t,t2)) xts t2,t)
  | App(e, es) ->
    let t1,s = inferTerm env s e in
    let ts,s = List.fold_right (fun e (ts,s) ->
      let t,s = inferTerm env s e in t::ts,s
    ) es ([],s) in
    let t = VarT(new_id()) in
    t, unify s (t1, List.fold_right(fun a b-> ArrT(a,b)) ts t)

let infer env fml : utype =
  ctx := M.empty;
  let fold env s =
    List.fold_left (fun (p,s) e ->
      let t,s = inferTerm env s e in ArrT(t,p),s
    ) (Prop,s)
  in
  let rec go env s = function
    | Top | Bottom -> s
    | Forall(t, fml) | Exist(t, fml) -> go env s fml
    | And(fml1, fml2) | Or(fml1, fml2) | Then(fml1, fml2) ->
      go env (go env s fml1) fml2
    | Pred(p, es) when M.mem p env ->
      let t,s = fold env s es in
      unify s (t,instantiate (M.find p env))
    | Pred(p, es) ->
      let t,s = fold env s es in
      ctx := M.add p t !ctx;
      s
  in
  let s = go env.types [] fml in
  Prop
