open FOL

type judgement = Judge of formula list * formula list

let show_judgement (Judge(assms, prop)) =
  "[" ^ show_formulas (List.rev assms) ^ "] |- [" ^ show_formulas prop ^ "]"
let show_judgements js = String.concat "\n" (List.map show_judgement js)

let formulize : judgement -> formula =
  fun (Judge(assms, props)) ->
  Then (List.fold_left (fun x y -> And(x,y)) Top assms,
        List.fold_left (fun x y -> Or(x,y)) Bottom props)

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
