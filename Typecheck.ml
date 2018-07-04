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

let rec fvT : utype -> int list = function
  | VarT(v) -> [v]
  | ConT(_, ts) -> unions (List.map fvT ts)
  | ArrT(t1, t2) -> union (fvT t1) (fvT t2)
  | Prop -> []

let rec unify1 : utype * utype -> utype -> utype = function
  | x,y when x = y -> (fun t->t)
  | ConT(con1, xs), ConT(con2, ys) when con1 = con2 && List.length xs = List.length ys ->
        let go (x,y) sbt t =
          unify1 (sbt x, sbt y) (sbt t)
        in
        List.fold_right go (List.combine xs ys) (fun t->t)
  | ConT(con1, xs), ConT(con2, ys) -> raise(UnificationFailed(ConT(con1, xs), ConT(con2, ys)))
  | ArrT(x1, x2), ArrT(y1, y2) ->
    let unif2 = unify1 (x2, y2) in
    let unif1 = unify1 (unif2 x1,unif2 y1) in
    (fun t -> unif1 (unif2 t))
  | VarT(i), t when not(List.mem i (fvT t)) -> substType i t
  | VarT(i), t when VarT i = t -> (fun x -> x)
  | VarT(i), t -> raise(UnificationFailed(VarT i, t))
  | t,VarT i -> unify1 (VarT i, t)
  | x,y -> raise (UnificationFailed(x, y))

let rec unify : (utype * utype) list -> utype -> utype = function
  | [] -> fun x -> x
  | (x,y)::qs ->
    let f = unify1 (x, y) in
    let qs' = List.map (fun (x,y) -> (f x, f y)) qs in
    (fun t -> f (unify qs' t))

let cnt = ref 0
let reset () = cnt := 0
let new_id () = cnt := !cnt + 1; !cnt

let utype_of_type t : utype =
  let ctx = ref M.empty in
  let rec f = function
    | VarT(i) when M.mem i !ctx -> VarT(M.find i !ctx)
    | VarT(i) -> let n = new_id () in ctx := M.add i n !ctx; VarT n
    | Prop -> Prop
    | ArrT(x, y) -> ArrT(f x,f y)
    | ConT(con, xs)-> ConT(con, List.map f xs)
  in
  f t

type ctx = utype M.t
let ctx = ref M.empty
let rec findUnifs env: term * utype -> (utype * utype) list = function
  | Var v, typ when M.mem v env.types -> [(typ,utype_of_type (M.find v env.types))]
  | Var v, typ when M.mem v !ctx -> [(typ,M.find v !ctx)]
  | Var v, typ -> ctx := M.add v typ !ctx; []
  | Abs(xs, t), typ ->
      let tyt = VarT(new_id()) in
      let tyxs = List.map (fun x -> (x,VarT(new_id()))) xs in
      ctx := List.fold_left (fun ctx (x,t) -> M.add x t ctx) !ctx tyxs;
      let qs = findUnifs env (t, tyt) in
      ctx := List.fold_left (fun ctx x -> M.remove x ctx) !ctx xs;
      (List.fold_right(fun (_,a) b -> ArrT(a,b)) tyxs tyt,typ)::qs
  | App(t, ts), typ ->
      let tyts = List.map (fun t -> (t,VarT(new_id()))) ts in
      let q = findUnifs env (t, (List.fold_right(fun (_,a) b-> ArrT(a,b)) tyts typ)) in
      List.fold_left (fun qs (t,u) -> let q = findUnifs env (t,u) in union qs q) q tyts

let inferTerm env term : utype =
  let typ0 = VarT(new_id()) in
  let s = findUnifs env (term, typ0) in
  unify s typ0

let infer env fml : utype =
  ctx := M.empty;
  let rec go = function
    | Pred(p, (ts : term list)), typ when M.mem p env.types ->
      let ptyp = utype_of_type (M.find p env.types) in
      let tyts = List.map (fun _ -> VarT(new_id())) ts in
      let tstyts = List.combine ts tyts in
      let qs = List.map (findUnifs env) tstyts in
      (typ,Prop)::(List.fold_right (fun x y->ArrT(x,y)) tyts typ,ptyp)::unions qs
    | Pred(p, ts), typ ->
      let tyts = List.map (fun _ -> VarT(new_id())) ts in
      let tstyts = List.combine ts tyts in
      let qs = List.map (findUnifs env) tstyts in
      ctx := M.add p (List.fold_right (fun x y -> ArrT(x, y)) tyts typ) !ctx;
      (typ,Prop)::unions (List.rev qs) 
    | Top, typ -> [(typ,Prop)]
    | Bottom, typ -> [(typ,Prop)]
    | And(fml1, fml2), typ -> (typ,Prop):: (union (go (fml1, typ)) (go (fml2, typ)))
    | Or(fml1, fml2), typ -> (typ,Prop):: (union (go (fml1, typ)) (go (fml2, typ)))
    | Then(fml1, fml2), typ -> (typ,Prop)::(union (go (fml1, typ)) (go (fml2, typ)))
    | Forall(t, fml), typ -> (typ,Prop)::go (fml, typ)
    | Exist(t, fml), typ -> (typ,Prop)::go (fml, typ)
  in
  let typ0 = VarT(new_id()) in
  let s = go (fml, typ0) in
  unify s typ0
