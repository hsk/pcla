open FOL
open LK
open Claire
open Env

exception NoSuchTheorem of ident
exception CannotApply of rule * judgement list
exception CannotInstantiate of exn
exception NoSuchCommand

type comSuspender =
  | ComAwait of env * (env * judgement list * command -> comSuspender * judgement list)
  | CommandError of string * exn * (judgement list -> comSuspender * judgement list)
  | ComReturn

let rec command env js: comSuspender * judgement list =
  if js = [] then ComReturn,[] else
  ComAwait(env,function
  | env,js,Apply rs ->
    begin try command env (judge (rs, js))
    with GoalError (r,js') -> CommandError("apply", CannotApply(r, js'), command env),js
    end
  | env,js,NoApply r ->
    begin try let _ = judge ([r], js) in command env js
    with GoalError (r,js') -> CommandError("noapply", CannotApply(r, js'), command env),js
    end
  | env,js,Use(idx, pairs) ->
    begin try
      let insts = List.fold_left (fun f (idt,pred) ->
        substPred ("?"^idt) pred f
      ) (M.find idx env.thms) pairs in
      let Judge(assms, props)::js = js in
      command env (Judge (insts::assms, props)::js)
    with err -> CommandError("use", NoSuchTheorem idx, command env),js
    end
  | env,js,Inst(idt, pred) ->
    begin match js with
    | [] -> CommandError("inst", Failure "empty judgement", command env),js
    | Judge(assm::assms, props)::js' ->
      try let r = substPred ("?"^idt) pred assm in command env (Judge(r::assms, props)::js')
      with err -> CommandError("inst", CannotInstantiate err, command env),js
    end
  | env,js,NewCommand("defer", ArgEmpty) -> command env ((fun (j::js) -> js @ [j]) js)
  | env,js,NewCommand(com, args) when M.mem com env.newcommands ->
    begin try
      let rec go = function
        | (CommandError(s, exn, err),js),_ -> raise exn
        | (ComReturn,js),_ -> js
        | (ComAwait(env,cont),js),[] -> js
        | (ComAwait(env,cont),js),c::coms -> go (cont (env, js, c),coms)
      in
      let coms = (M.find com env.newcommands) env args js in
      command env (go (command env js,coms))
    with Not_found -> CommandError(com, NoSuchCommand, fun js -> command env js),js
       | err -> CommandError(com, err, fun js -> command env js),js
    end
  ),js

exception MlFileLoadError of string
exception TypeError of formula * exn
exception NoSuchDecl of exn

type declSuspender =
  | DeclAwait of (decl * env -> declSuspender * env)
  | ProofNotFinished of judgement list * (command * env -> declSuspender * env)
  | RunCommandError of ident * exn * (env -> declSuspender * env)
  | DeclError of ident * exn * (env -> declSuspender * env)

let showDeclSuspender = function
  | DeclAwait _ -> "DeclAwait"
  | ProofNotFinished(js, _) -> Printf.sprintf "ProofNotFinished:\n%s" (show_judgements js)
  | RunCommandError(idt,err,_) -> Printf.sprintf "RunCommandError(%s): %s" idt (Printexc.to_string err)
  | DeclError(i,err,_) -> Printf.sprintf "DeclError(%s): %s" i (Printexc.to_string err)

let rec toplevel env : declSuspender * env =
  DeclAwait(function
    | AxiomD(idx, fml),env ->
      begin try Typing.infer env fml; toplevel (insertThm idx fml env)
      with err -> DeclError("typecheck",TypeError(fml, err),toplevel),env
      end
    | ThmD(idx, fml, Proof coms),env ->
      begin try Typing.infer env fml;
        let newGoal : formula -> judgement list = fun fml -> [Judge([], [fml])] in
        let env = { env with proof = [] } in
        let rec go = function
          | (ComReturn,js'),coms -> toplevel (insertThm idx fml env)
          | (CommandError(idt, err, cont),js'),coms ->
            RunCommandError(idt, err, fun env -> go (cont js',coms)),env
          | (ComAwait(env',cont),js'),[] ->
            ProofNotFinished(js', fun (com',env) -> go ((ComAwait (env,cont),js'),[com'])),env
          | (ComAwait(env',cont),js'),com::coms -> go(cont(env,js',com),coms)
        in
        go (command env (newGoal fml),coms)
      with err -> DeclError("typecheck",TypeError(fml, err),toplevel),env
      end
    | ImportD path,env ->
      toplevel (claire env (let Laire ds = Lexer.pLaire (Lexer.readFile path) in ds))
    | ConstD(p, typ),env -> toplevel { env with types = M.add p typ env.types }
    | PrintProof,env -> Printf.printf "%s\n" (print_proof env); toplevel env
    | MlFile file,env ->
      begin try let (ds,cs)=M.find file env.hs in
        toplevel {env with
          newdecls = M.union (fun k a b -> Some b)(M.fromList ds) env.newdecls;
          newcommands = M.union (fun k a b -> Some b)(M.fromList cs) env.newcommands};
      with Not_found -> DeclError("MlFile", MlFileLoadError file, toplevel),env
      end
    | NewDecl(dec, args),env -> try
        let rec go = function
          | (DeclAwait cont,env),[] -> toplevel env
          | (DeclAwait cont,env),d::ds -> go (cont(d,env),ds)
          | (err,_),_ -> failwith ("declrunner: " ^ showDeclSuspender err)
        in
        go (toplevel env,(M.find dec env.newdecls) args)
      with err -> DeclError(dec, NoSuchDecl err, toplevel),env
  ),env
and claire env decls =
  let rec go = function
    | (DeclAwait cont,env),[] -> env
    | (DeclAwait cont,env),d::ds -> go(cont (d,env),ds) 
    | (z,env),_ -> Printf.printf "%s\n" (showDeclSuspender z); env
  in
  go (toplevel env,decls)
