open FOL
open LK

type thmIndex = string
type pairs = (ident * predicate) list
let show_pair (x, p) = Printf.sprintf "(%s,%s)" x (show_predicate p)
let show_pairs pairs = String.concat ", " (List.map show_pair pairs)
type argument =
  | ArgEmpty
  | ArgPreds of predicate list
  | ArgTerms of term list
  | ArgTyped of ident * type_
  | ArgIdents of (ident * pairs) list
let show_xpairs (x,pairs) = Printf.sprintf "(%s,[%s])" x (show_pairs pairs)
let show_xpairss xpairss = String.concat ", " (List.map show_xpairs xpairss)
let show_argument = function
  | ArgEmpty -> "ArgEmpty"
  | ArgPreds(ps) -> Printf.sprintf "ArgPreds([%s])" (show_predicates ps)
  | ArgTerms(ts) -> Printf.sprintf "ArgTerms([%s])" (show_terms ts)
  | ArgTyped(x,t) -> Printf.sprintf "ArgTyped(%s, %s)" x (show_type t)
  | ArgIdents(xpss) -> Printf.sprintf "ArgIdents([%s])" (show_xpairss xpss)
let show_arguments arguments = String.concat ", " (List.map show_argument arguments)

type command =
  | Apply of rule list
  | Use of thmIndex * pairs
  | Inst of ident * predicate
  | NoApply of rule
  | NewCommand of ident * argument
let show_command = function
  | Apply(rs) -> Printf.sprintf "Apply([%s])" (show_rules rs)
  | Use(x,ps) -> Printf.sprintf "Use(%s, [%s])" x (show_pairs ps)
  | Inst(x,p) -> Printf.sprintf "Inst(%s, %s)" x (show_predicate p)
  | NoApply(r) -> Printf.sprintf "NoApply(%s)" (show_rule r)
  | NewCommand(x,a) -> Printf.sprintf "NewCommand(%s, %s)" x (show_argument a)
let show_commands commands = String.concat ", " (List.map show_command commands)

type proof =
  | Proof of command list
let show_proof = function
  | Proof commands -> Printf.sprintf "Proof([%s])" (show_commands commands)

type decl =
  | ThmD of thmIndex * formula * proof
  | AxiomD of thmIndex * formula
  | ImportD of string
  | PrintProof
  | ConstD of ident * type_
  | MlFile of string
  | NewDecl of ident * argument list
let show_decl = function
  | ThmD(x,f,p) -> Printf.sprintf "ThmD(%s, %s, %s)" x (show_formula f) (show_proof p)
  | AxiomD(x,f) -> Printf.sprintf "AxiomD(%s, %s)" x (show_formula f)
  | ImportD(x) -> Printf.sprintf "ImportD(%s)" x
  | PrintProof -> Printf.sprintf "PrintProof"
  | ConstD(x,t) -> Printf.sprintf "ConstD(%s, %s)" x (show_type t)
  | MlFile(x) -> Printf.sprintf "MlFile(%s)" x
  | NewDecl(x,arguments) -> Printf.sprintf "NewDecl(%s, [%s])" x (show_arguments arguments)
let show_decls decls = String.concat ", " (List.map show_decl decls)

type laire = Laire of decl list
let show_laire = function
  | Laire decls -> Printf.sprintf "Laire([%s])" (show_decls decls)
