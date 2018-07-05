open FOL
open LK
open Claire
module M = struct
  module M = Map.Make (struct
    type t = string
    let compare = compare
  end)
  include M
  let keys m = List.map(fun (k,_)->k) (M.bindings m)
  let fromList ls = List.fold_left(fun m (k,v)->M.add k v m) M.empty ls
end
let show_formula_map thms =
  let es = M.bindings thms in
  String.concat ", " (List.map (fun (x,f) -> Printf.sprintf "%s:%s" x (show_formula f)) es)

let show_type_map types =
  let es = M.bindings types in
  String.concat ", " (List.map (fun (x,f) -> Printf.sprintf "%s:%s" x (show_type f)) es)

let show_proof_map proof =
  String.concat ", " (List.map (fun (c,x) -> Printf.sprintf "%s:%s" (show_command c) x) proof)

type env = {
  thms : formula M.t;
  types : type_ M.t;
  proof : (command * string) list;
  newcommands : defCommand M.t;
  newdecls : (argument list -> decl list) M.t;
  hs : ((string * (argument list -> decl list)) list * (string * defCommand) list) M.t;
}
and defCommand = env -> argument -> judgement list -> command list

let show_env env =
  Printf.sprintf "{thms = [%s], types = [%s], proof = %s, newcommands: [%s], newdecls = [%s]}"
  (show_formula_map env.thms)
  (show_type_map env.types)
  (show_proof_map env.proof)
  (String.concat ", " (M.keys env.newcommands))
  (String.concat ", " (M.keys env.newdecls))
let defEnv : env = {thms=M.empty;types=M.empty;proof=[];newcommands=M.empty;newdecls=M.empty;hs=M.empty}

let print_proof : env -> string =
fun env -> Printf.sprintf "= proof of the previous theorem =\nproof\n%s\nqed\n" 
  (String.concat "\n" (List.map (fun (_,x) -> "  " ^ x) (List.filter (function (NoApply _,_)-> false | _ -> true) env.proof)))

let insertThm : thmIndex -> formula -> env -> env = 
  fun idx fml env ->
  let rec metagen : formula -> formula = function
    | Pred(p, ts) when M.mem p env.types -> Pred(p, ts)
    | Pred(p, ts) -> Pred("?" ^ p, ts)
    | Top -> Top
    | Bottom -> Bottom
    | And(fml1, fml2) -> And(metagen fml1, metagen fml2)
    | Or(fml1, fml2) -> Or(metagen fml1, metagen fml2)
    | Then(fml1, fml2) -> Then(metagen fml1, metagen fml2)
    | Forall(v, fml) -> Forall(v, metagen fml)
    | Exist(v, fml) -> Exist(v, metagen fml)
  in
  {env with thms = M.add idx (metagen fml) (env.thms) }
