open FOL

type judgement = Judge of formula list * formula list
type assmIndex = string
type rule =
  | I | Cut of formula
  | AndL1 | AndL2 | AndR
  | OrL | OrR1 | OrR2
  | ImpL | ImpR
  | BottomL | TopR
  | ForallL of term | ForallR of ident
  | ExistL of ident | ExistR of term
  | WL | WR
  | CL | CR
  | PL of int | PR of int

let show_judgement (Judge(assms, prop)) =
  "[" ^ show_formulas (List.rev assms) ^ "] |- [" ^ show_formulas prop ^ "]"
let show_judgements js = String.concat "\n" (List.map show_judgement js)
let show_rule = function
  | I -> Printf.sprintf "I"
  | Cut(f) -> Printf.sprintf "Cut(%s)" (show_formula f)
  | AndL1 -> Printf.sprintf "AndL1"
  | AndL2 -> Printf.sprintf "AndL2"
  | AndR -> Printf.sprintf "AndR"
  | OrL -> Printf.sprintf "OrL"
  | OrR1 -> Printf.sprintf "OrR1"
  | OrR2 -> Printf.sprintf "OrR2"
  | ImpL -> Printf.sprintf "ImpL"
  | ImpR -> Printf.sprintf "ImpR"
  | BottomL -> Printf.sprintf "BottomL"
  | TopR -> Printf.sprintf "TopR"
  | ForallL(t) -> Printf.sprintf "ForallL(%s)" (show_term t)
  | ForallR(x) -> Printf.sprintf "ForallR(%S)" x
  | ExistL(x) -> Printf.sprintf "ExistL(%S)" x
  | ExistR(t) -> Printf.sprintf "ExistR(%s)" (show_term t)
  | WL -> Printf.sprintf "WL"
  | WR -> Printf.sprintf "WR"
  | CL -> Printf.sprintf "CL"
  | CR -> Printf.sprintf "CR"
  | PL(i) -> Printf.sprintf "PL(%d)" i
  | PR(i) -> Printf.sprintf "PR(%d)" i
let show_rules rules = String.concat ", " (List.map show_rule rules)

exception GoalError of rule * judgement list

let rec deleteAt k xs = match k,xs with
  | k,[] -> []
  | 0,x::xs -> xs
  | k,x::xs -> x::deleteAt (k-1) xs

let rec judge = function
  | I::r, Judge(a, p)::j when a = p -> judge(r,j)
  | Cut f::r, Judge(a, p)::j -> judge(r,Judge(a,f::p)::Judge(f::a, p)::j)
  | AndL1::r, Judge(And(f, _)::a, p)::j -> judge(r,Judge(f::a, p)::j)
  | AndL2::r, Judge(And(_, f)::a, p)::j -> judge(r,Judge(f::a, p)::j)
  | AndR::r, Judge(a, And(f1, f2)::p)::j -> judge(r,Judge(a,f1::p)::Judge(a,f2::p)::j)
  | OrL::r, Judge(Or(f1,f2)::a,p)::j -> judge(r,Judge(f1::a, p)::Judge(f2::a, p)::j)
  | OrR1::r, Judge(a, Or(f,_)::p)::j -> judge(r,Judge(a,f::p)::j)
  | OrR2::r, Judge(a, Or(_,f)::p)::j -> judge(r,Judge(a,f::p)::j)
  | ImpL::r, Judge(Then(f1, f2)::a, p)::j -> judge(r,Judge(a,f1::p)::Judge(f2::a, p)::j)
  | ImpR::r, Judge(a, Then(f1, f2)::p)::j -> judge(r,Judge(f1::a, f2::p)::j)
  | BottomL::r, Judge(Bottom::a, p)::j -> judge(r,j)
  | TopR::r, Judge(a, Top::p)::j -> judge(r,j)
  | ForallL t::r, Judge(Forall(x, f)::a, p)::j -> judge(r,Judge(substTerm x t f::a, p)::j)
  | ForallR y::r, Judge(a, Forall(x, f)::p)::j -> judge(r,Judge(a,substTerm x (Var y) f::p)::j)
  | ExistL y::r, Judge(Exist(x, f)::a, p)::j -> judge(r,Judge(substTerm x (Var y) f::a, p)::j)
  | ExistR t::r, Judge(a, Exist(x, f)::p)::j -> judge(r,Judge(a,substTerm x t f::p)::j)
  | WL::r, Judge(_::a, p)::j -> judge(r,Judge(a, p)::j)
  | WR::r, Judge(a, _::p)::j -> judge(r,Judge(a, p)::j)
  | CL::r, Judge(f::a, p)::j -> judge(r,Judge(f::f::a, p)::j)
  | CR::r, Judge(a, f::p)::j -> judge(r,Judge(a, f::f::p)::j)
  | PL k::r, Judge(a, p)::j when k < List.length a -> judge(r,Judge(List.nth a k::deleteAt k a, p)::j)
  | PR k::r, Judge(a, p)::j when k < List.length p -> judge(r,Judge(a, List.nth p k::deleteAt k p)::j)
  | [], j -> j
  | r::_, j -> raise (GoalError (r,j))
