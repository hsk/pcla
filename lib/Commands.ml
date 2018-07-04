open FOL
open LK
open Claire
open Env

exception CannotSolve of judgement list
exception FailedToApply
exception WrongArgument of argument
exception WrongArguments of argument list

let rec replicate i v =
  if i = 0 then []
  else v :: replicate (i-1) v

let findIndex f ls =
  let rec g = function
    | n,x::_ when f x-> Some n
    | n,_::xs -> g (n+1,xs)
    | _,_ -> None
  in
  g (0,ls)
let elemIndex e = findIndex(fun a-> e=a)

let onlyL : int -> int -> rule list =
  fun i n -> List.concat (replicate i [WL] @ replicate (n-i-1) [PL 1; WL])

let onlyR : int -> int -> rule list =
  fun i n -> List.concat (replicate i [WR] @ replicate (n-i-1) [PR 1; WR])

let assumption : env -> argument -> judgement list -> command list =
fun env ArgEmpty js ->
  match js with
  | Judgement(assms, props)::_ ->
    begin match findIndex (fun a -> List.mem a assms) props with
    | None -> raise (CannotSolve js)
    | Some i ->
      let Some j = elemIndex (List.nth props i) assms in
      [Apply(onlyR i (List.length props) @ onlyL j (List.length assms) @ [I])]
    end
  | _ -> raise (WrongArgument ArgEmpty)

(*| implyR

thm: a ==> b
goal: assms |- b, props

use thm
  assms, a ==> b |- b, props
apply ImpL
  assms |- a, b, props
  assms, b |- b, props
defer
  assms, b |- b, props
  assms |- a, b, props
assumption
  assms |- a, b, props
apply (PR 1, WR)
  assms |- a, props
*)
let rec implyR : env -> argument -> judgement list -> command list =
  fun env arg js -> match arg with
  | ArgIdents [(i,ps)] -> Use(i, ps) :: implyR env ArgEmpty js
  | ArgEmpty -> 
    [ Apply [ImpL];
      NewCommand("defer", ArgEmpty);
      NewCommand("assumption", ArgEmpty);
      Apply [PR 1; WR];
    ]
  | arg -> raise (WrongArgument arg)

(*| implyL

thm: a ==> b
goal: assms, a |- props

use thm
  assms, a, a ==> b |- props
apply ImpL
  assms, a |- a, props
  assms, a, b |- props
assumption
  assms, a, b |- props
apply (PL 1, WL)
  assms, b |- props
*)
let rec implyL : env -> argument -> judgement list -> command list =
  fun env arg js -> match arg with
  | ArgIdents [i,ps] -> Use(i, ps) :: implyL env ArgEmpty js
  | ArgEmpty -> [Apply[ImpL];NewCommand("assumption", ArgEmpty);Apply[PL 1; WL]]
  | arg -> raise (WrongArgument arg)

(*| genR

goal: assms |- P(a), props

apply Cut [Forall a. P(a)]
  assms |- Forall a. P(a), P(a), props
  assms, Forall a. P(a) |- P(a), props
defer
  assms, Forall a. P(a) |- P(a), props
  assms, |- Forall a. P(a), P(a), props
apply (ForallL [a])
  assms, P(a) |- P(a), props
  assms, |- Forall a. P(a), P(a), props
assumption
  assms, |- Forall a. P(a), P(a), props
apply (PR 1, WR)
  assms, |- Forall a. P(a), props
*)
let genR : env -> argument -> judgement list -> command list =
  fun env arg js -> match arg,js with
  | ArgIdents [(i,[])], Judgement(_, (p::_))::_ ->
    [ Apply [Cut(Forall(i, p))];
      NewCommand("defer", ArgEmpty);
      Apply [ForallL(Var i)];
      NewCommand("assumption", ArgEmpty);
      Apply [PR 1; WR];
    ]
  | arg, _ -> raise (WrongArgument arg)

(*| genL

goal: assms, P(a) |- props

apply Cut [Forall a. P(a)]
  assms, P(a) |- Forall a. P(a), props
  assms, P(a), Forall a. P(a) |- props
apply (ForallR [a])
  assms, P(a) |- P(a), props
  assms, P(a), Forall a. P(a) |- props
assumption
  assms, P(a), Forall a. P(a) |- props
apply (PL 1, WR)
  assms, Forall a. P(a) |- props
*)
let genL : env -> argument -> judgement list -> command list =
  fun env arg js -> match arg,js with
  | ArgIdents [(i,[])], Judgement(p::ps,_)::_ -> 
    [ Apply [Cut(Forall(i, p))];
      Apply [ForallR i];
      NewCommand("assumption", ArgEmpty);
      Apply [PL (List.length ps); WL];
    ]
  | arg, _ -> raise (WrongArgument arg)

(*| absR

goal: assms, a |- b, props

apply Cut [a ==> b]
  assms, a |- a ==> b, b, props
  assms, a, a ==> b |- b, props
defer
  assms, a, a ==> b |- b, props
  assms, a |- a ==> b, b, props
apply ImpL
  assms, a |- a, b, props
  assms, a, b |- b, props
  assms, a |- a ==> b, b, props
assumption [2]
  assms, a |- a ==> b, b, props
apply (PR 1, WR, WL)
  assms |- a ==> b, props
*)

let absL : env -> argument -> judgement list -> command list =
fun env arg js -> match arg,js with
  | ArgEmpty, Judgement(a::_, (b::_))::_ ->
    [ Apply [Cut(Then(a,b))];
      NewCommand("defer", ArgEmpty);
      Apply [ImpL];
      NewCommand("assumption", ArgEmpty);
      NewCommand("assumption", ArgEmpty);
      Apply [PR 1; WR; WL];
    ]
  | arg, _ -> raise (WrongArgument arg)

let export_command : (string * (env -> argument -> judgement list -> command list)) list = [
  "assumption", assumption;
  "implyR", implyR;
  "implyL", implyL;
  "genR", genR;
  "genL", genL;
  "absL", absL;
]

(* --------------------------------------------- *)

let definition : argument list -> decl list = function
  | [ArgTyped(i, typ); ArgPreds[PredFml body]] -> [ConstD(i, typ); AxiomD(i ^ "_def", body)]
  | arg -> Printf.printf "arg=%s\n" (show_arguments arg); raise (WrongArguments arg)
let export_decl = ["definition", definition]
