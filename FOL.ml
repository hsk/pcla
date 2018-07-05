type ident = string
type term =
  | Var of ident
  | Abs of ident list * term
  | App of term * term list
type formula =
  | Pred of ident * term list
  | Top
  | Bottom
  | And of formula * formula
  | Or of formula * formula
  | Then of formula * formula
  | Forall of ident * formula
  | Exist of ident * formula
let const c = Pred(c, [])
let neg a = Then(a, Bottom)
type predicate
  = PredFun of ident list * predicate
  | PredFml of formula
type 'a typeForm
  = VarT of 'a
  | ConT of ident * 'a typeForm list
  | ArrT of 'a typeForm * 'a typeForm 
  | Prop
type type_ = ident typeForm

let show_idents xs = String.concat ", " (List.map(Printf.sprintf "%S") xs)
let rec show_term = function
  | Var x -> Printf.sprintf "Var(%S)" x
  | Abs(xs,t) -> Printf.sprintf "Abs([%s],%s)" (show_idents xs) (show_term t)
  | App(t,ts) -> Printf.sprintf "App(%s,[%s])" (show_term t) (show_terms ts) 
and show_terms ts = String.concat ", " (List.map show_term ts)
let rec show_formula = function
  | Pred(x,ts) -> Printf.sprintf "Pred(%S,[%s])" x (show_terms ts)
  | Top -> "Top"
  | Bottom -> "Bottom"
  | And(f1, f2) -> Printf.sprintf "(%s :/\\: %s)" (show_formula f1) (show_formula f2)
  | Or(f1, f2) -> Printf.sprintf "(%s :\\/: %s)" (show_formula f1) (show_formula f2)
  | Then(f1, f2) -> Printf.sprintf "(%s :==>: %s)" (show_formula f1) (show_formula f2)
  | Forall(x, f) -> Printf.sprintf "Forall(%S,%s)" x (show_formula f)
  | Exist(x, f) -> Printf.sprintf "Exist(%S,%s)" x (show_formula f) 
let show_formulas fs = String.concat ", " (List.map show_formula fs)
let rec show_predicate = function
  | PredFun(xs,p) -> Printf.sprintf "Pred([%s],%s)" (show_idents xs) (show_predicate p)
  | PredFml(f) -> Printf.sprintf "PredFml(%s)" (show_formula f)
let show_predicates ps = String.concat ", " (List.map show_predicate ps)
let rec show_tf show_a = function
  | VarT a -> Printf.sprintf "VarT(%S)" (show_a a)
  | ConT(x,tfs) -> Printf.sprintf "ConT(%S, [%s])" x (show_tfs show_a tfs) 
  | ArrT(tf1,tf2) -> Printf.sprintf "ArrT(%s, %s)" (show_tf show_a tf1) (show_tf show_a tf2)
  | Prop -> Printf.sprintf "Prop"
and show_tfs show_a tfs = String.concat ", " (List.map (show_tf show_a) tfs)
let show_type = show_tf (fun x->x)

let substType : 'a -> 'a typeForm -> 'a typeForm -> 'a typeForm =
fun x t' ->
  let rec go = function
  | VarT y when x = y -> t'
  | VarT y -> VarT y
  | ConT(y, ts) -> ConT(y, List.map go ts)
  | ArrT(y1, y2) -> ArrT(go y1, go y2)
  | Prop -> Prop
  in go

let substTerm : ident -> term -> formula -> formula =
fun idt t' ->
  let rec got = function
    | Var i when i = idt -> t'
    | Var i -> Var i
    | Abs(ids, t) when List.mem idt ids -> Abs(ids, t)
    | Abs(ids, t) -> Abs(ids, got t)
    | App(tx, tys) -> App(got tx, List.map got tys)
  in
  let rec go = function
    | Pred(p, ts) -> Pred(p, List.map got ts)
    | Top -> Top
    | Bottom -> Bottom
    | And(f1, f2) -> And(go f1, go f2)
    | Or(f1, f2) -> Or(go f1, go f2)
    | Then(f1, f2) -> Then(go f1, go f2)
    | Forall(x, fml) -> Forall(x, go fml)
    | Exist(x, fml) -> Exist(x, go fml)
  in go

exception ArgumentsNotFullyApplied of predicate
exception CannotApplyToFormula of term list * formula

let substPred : ident -> predicate -> formula -> formula =
fun idt pred ->
  let rec sbterm t x = function
    | PredFun(ys, fml) -> PredFun(ys, sbterm t x fml)
    | PredFml(fml) -> PredFml(substTerm t x fml)
  and beta : term list * predicate -> formula = function
    | xs, PredFun([], p) -> beta (xs, p)
    | [], (PredFun(_, _) as z) -> raise (ArgumentsNotFullyApplied z)
    | [], PredFml(fml) -> fml
    | x::xs, PredFun(t::ts,fml) -> beta (xs, PredFun(ts, sbterm t x fml))
    | xs, PredFml(fml) -> raise(CannotApplyToFormula(xs, fml))
  in
  let rec go : formula -> formula = function
    | Pred(idt_, ts) when idt = idt_ -> beta (ts, pred)
    | Pred(_, _) as z -> z
    | Top -> Top
    | Bottom -> Bottom
    | And(fml1, fml2) -> And(go fml1, go fml2)
    | Or(fml1, fml2) -> Or(go fml1, go fml2)
    | Then(fml1, fml2) -> Then(go fml1, go fml2)
    | Forall(v, fml) -> Forall(v, go fml)
    | Exist(v,fml) -> Exist(v, go fml)
  in go
