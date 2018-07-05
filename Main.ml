open Claire
open Parser
open Env
open Checker
open Printf

let defEnv = {defEnv with hs=M.fromList [
  "Commands.ml",(Commands.export_decl,Commands.export_command);
  "EqCommands.ml",(EqCommands.export_decl,EqCommands.export_command)]
}
let rec init = function
  | [a] -> []
  | x::xs -> x::init xs

let clairepl : env -> unit =
fun env ->
  let rec safep : (unit -> unit) -> (string -> 'a) -> 'a =
    fun ma p ->
      ma ();
      try p(read_line())
      with err -> (*print (err :: ErrorCall);*)safep ma p
  in
  let rec go : env -> (unit -> declSuspender) -> unit = fun env k ->
    let (z,env') = runStateT k env in
    match z with
    | DeclReturn -> go env' k
    | DeclAwait k ->
      let t = safep (fun ()->printf "decl>%@") pDecl in
      go env' (fun()->k t)
    | ProofNotFinished(js, cont) ->
      List.iter (fun j -> Printf.printf "%s\n" (LK.show_judgement j)) js;
      (*
      let (t,raw) = safep (fun () -> printf "command>%@") (fun s -> let s' = pCommand s in seq s' (s',s)) in
      go { env' with proof = env'.proof @ [t,raw] } (cont t)
      *)
    | RunCommandError idt (*err cont*) ->
      printf "%s\n" (showDeclSuspender z)
      (* if env'.proof = [] then go env' cont else go ({env' with proof = init (env'.proof)}) cont *)
    | DeclError((*idt,*) err (*,cont*)) ->
      printf "%s\n" err
      (*;go env cont*)
  in
  go env toplevelM

let _ =
  if Array.length Sys.argv != 2 then
    begin
      printf "=========================\n";
      printf "=== Welcome to Claire ===\n";
      printf "=========================\n";
      printf "\n";
      clairepl defEnv
    end
  else
    begin
      let str = readFile Sys.argv.(1) in
      let Laire ds = pLaire str in
      let env = claire defEnv ds in
      printf "= Constants =\n";
      List.iter (fun(k,v)->printf "(%S,%s)\n" k (FOL.show_type v)) (M.bindings env.types);(* todo *)
      printf "= Proved Theorems =\n";
      List.iter (fun(k,v)->printf "(%S,%s)\n" k (FOL.show_formula v)) (M.bindings env.thms);
    end