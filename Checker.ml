open FOL
open LK
open Claire
open Env
open Typecheck
open CheckerCommand
open Printf
let pLaire : string -> laire = fun str -> Parser.laire Lexer.tokens (Lexing.from_string str)
let pDecl : string -> decl = fun str -> Parser.decl Lexer.tokens (Lexing.from_string str)
let pCommand : string -> command = fun str -> Parser.command Lexer.tokens (Lexing.from_string str)
let pFormula : string -> formula = fun str -> Parser.formula Lexer.tokens (Lexing.from_string str)
let pTerm : string -> term = fun str -> Parser.term Lexer.tokens (Lexing.from_string str)
let newGoal : formula -> judgement list = fun fml -> [Judgement([], [fml])]

let readFile f =
  let ic = open_in f in
  let n = in_channel_length ic in
  let s = String.create n in
  really_input ic s 0 n;
  close_in ic;
  s

let env = ref Env.defEnv
let runStateT m env' =
  env := env';
  let result = m () in
  (result, !env)

(*
type 'y declSuspender
  = DeclAwait of (Decl -> y)
  | ProofNotFinished of [Judgement] (Command -> y)
  | RunCommandError of Ident SomeException y
  | DeclError of Ident SomeException y
  deriving (Functor)
*)
type declSuspender =
  | DeclAwait of (decl -> unit -> declSuspender)
  | ProofNotFinished of judgement list * (command -> declSuspender)
  | RunCommandError of ident
  | DeclError of ident
  | DeclReturn

let forever : (unit -> declSuspender) -> (unit -> declSuspender) =
  fun f () ->
  let rec g = function
    | DeclReturn -> g (f ())
    | DeclAwait f -> DeclAwait (fun decl _-> g(f decl ()))
    | r -> r
  in
  g (f ())

(*
type declError
  = IllegalPredicateDeclaration Formula
  | IllegalTermDeclaration Term
  | MlFileLoadError InterpreterError
  | TypeError Formula SomeException
  | NoSuchDecl
  deriving (Show)

instance Exception DeclError
*)
let showDeclSuspender = function
  | DeclAwait _ -> "DeclAwait"
  | ProofNotFinished(js, _) -> "ProofNotFinished:\n" ^ (show_judgements js)
  | RunCommandError idt (*err _*) -> "RunCommandError(" ^ idt ^ ")" (*^ ": " ^  err *)
  | DeclError (* i *) err -> "DeclError(" (* ^ i ^ "): "*) ^ err ^ ")"
  | DeclReturn -> "DeclReturn"

let typecheck : formula -> utype -> (unit -> declSuspender) -> declSuspender =
  fun fml u k ->
  try match infer !env fml with
    | typ when u = typ -> k ()
    | typ -> DeclError("typecheck" (*(toException $ TypeError fml (toException $ UnificationFailed u typ)) (return ())*))
  with
  | UnificationFailed(t1,t2) -> DeclError(sprintf "typecheck unification failed (%s, %s)" (show_utype t1) (show_utype t2))
  | NotFound (x,env) -> DeclError(sprintf "typecheck not found %s" x)
  | Not_found -> DeclError(sprintf "typecheck not found")
  | err -> DeclError("typecheck2" (*(toException $ TypeError fml err) (return ())*))

let rec toplevelM : unit -> declSuspender = fun () -> forever toplevelM1 ()
and toplevelM1 : unit -> declSuspender =
  fun () ->
  DeclAwait(fun decl () ->
  match decl with
    | AxiomD(idx, fml) -> typecheck fml Prop (fun () ->
        env := insertThm idx fml !env;
        DeclReturn
      )
    | ThmD(idx, fml, Proof coms) -> typecheck fml Prop (fun () ->
        env := {!env with proof = []};
        runThmD idx fml coms
      )
    | ImportD path ->
      env := claire !env (let Laire ds = pLaire (readFile path) in ds);
      DeclReturn
    | ConstD(p, typ) ->
      env := { !env with types = M.add p typ !env.types };
      DeclReturn
    | PrintProof -> DeclReturn
    | MlFile file ->
      begin try
        let (ds,cs)=M.find file !env.hs in
        env := {!env with
          newdecls = M.union (fun k a b -> Some b)(M.fromList ds) !env.newdecls;
          newcommands = M.union (fun k a b -> Some b)(M.fromList cs) !env.newcommands};
        DeclReturn
      with Not_found -> DeclError "MlFile"
      end
    | NewDecl(dec, args) ->
      begin try
        let rec go cr ds =
          match cr () with
          | DeclAwait k ->
            begin match ds with
            | [] -> DeclReturn
            | c::cs' -> go (k c) cs'
            end
          | DeclReturn -> DeclReturn
          | DeclError err -> failwith ("declrunner: " ^ err)
          | RunCommandError err -> failwith ("declrunner: " ^ err)
        in
        go toplevelM ((M.find dec !env.newdecls) args)
      with
      | Not_found -> DeclError("not found " ^ dec (*err (return ())*))
      (*| err -> DeclError(dec ^ " kore"(*err (return ())*))*)
      end
  )

and runThmD : thmIndex -> formula -> command list -> declSuspender =
fun idx fml coms ->
      let next = fun () ->
        env:=insertThm idx fml !env;
        DeclReturn
      in
      let rec go : (unit -> comSuspender) -> judgement list -> command list -> declSuspender =
        fun machine js coms ->
          put js;
          let result = machine () in
          let js' = get () in
          match result with
          | ComReturn -> next ()
          | ComAwait cont ->
              begin match coms with
              | [] -> ProofNotFinished(js', fun com' -> go (fun ()->ComAwait cont) js' [com'])
              | c::cs -> go (cont c) js' cs
              end
          | CommandError(idt, (*err cont*) cont) as z -> RunCommandError(idt (*,err (return ()) fun () -> go cont js' coms)*))
      in
      env := { !env with proof = [] };
      go (commandM !env) (newGoal fml) coms;(* todo: next declsuspender *)

and claire : env -> decl list -> env = fun env decls ->
  let rec go : (unit -> declSuspender) -> env -> decl list -> env =
  fun machine env decls ->
    let (result,env') = runStateT machine env in
    match result with
    | DeclAwait cont ->
      begin match decls with
      | [] -> env'
      | d::ds -> go (cont d) env' ds 
      end
    | z -> Printf.printf "%s\n" (showDeclSuspender z); env'
  in
  go toplevelM env decls
