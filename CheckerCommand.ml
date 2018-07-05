open FOL
open LK
open Claire
open Env
open Typecheck
exception GoalError of rule * judgement list

let rec deleteAt k xs = match k,xs with
  | k,[] -> []
  | 0,x::xs -> xs
  | k,x::xs -> x::deleteAt (k-1) xs

let rec judge : rule list * judgement list -> judgement list = function
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
(*--*)

type comSuspender =
  | ComAwait of (command -> comSuspender)
  | CommandError of string * (unit -> comSuspender)
  | ComReturn

let js = ref []
let put js' = js := js'
let get () = !js
let modify f = js := f !js
(*
instance Show (comSuspender y) where
  show (ComAwait _) = "ComAwait"
  show (CommandError com err _) = com ++ ": " ++ show err

exception NoSuchTheorem of ident
exception CannotApply of rule * judgement
exception CannotInstantiate of someException
exception NewCommandError of argument * someException
exception NoSuchCommand
*)


let rec comrunner : env -> command list -> unit =
fun env cs ->
  let rec go cr cs =
    match cr () with
    | CommandError(s, err) -> failwith s
    | ComReturn -> ()
    | ComAwait k ->
      match cs with
      | [] -> ()
      | c::cs' -> go (fun()->k c) cs'
  in
  go (fun () -> commandM env) cs
and commandM : env -> comSuspender =
fun env ->
  ComAwait(fun com ->
  let insts fml pairs =
    List.fold_left (fun f (idt,pred) -> substPred ("?"^idt) pred f) fml pairs
  in
  let next () =
    if get () = [] then ComReturn else commandM env
  in
  let js = get() in
  match com with
    | Apply rs ->
      begin try
        put (judge (rs, js));
        next()
      with GoalError (r,js') ->
        CommandError("apply", (* (toException $ CannotApply r js') (return ()) *) fun _ ->
          commandM env; next ())
      end
    | NoApply r ->
      begin try
        let _ = judge ([r], js) in next ()
      with GoalError (r,js') ->
          CommandError("noapply", (*(toException $ CannotApply r js') (return ()) *) fun _ ->
          commandM env; next ())
      end
    | Use(idx, pairs) when M.mem idx env.thms ->
      begin try
        let fml = M.find idx env.thms in
        let r = insts fml pairs in
        modify (fun (Judge(assms, props)::js) -> Judge (r::assms, props)::js);
        next ()
      with err -> CommandError("inst", (*(toException $ CannotInstantiate err) (return ())*) fun _ -> next())
      end
    | Use(idx, pairs) ->
      CommandError("use", (*(toException $ NoSuchTheorem idx) (return ())*) fun _ -> next())
    | Inst(idt, pred) ->
      begin match js with
        | [] -> CommandError("inst", (*(toException (error "empty judgement"::ErrorCall)) (return ())*) fun _ -> next())
        | Judge(assm::assms, props)::js' ->
          try
            let r = substPred ("?"^idt) pred assm in
            put (Judge(r::assms, props)::js');
            next ()
          with err -> CommandError("inst", (*(toException $ CannotInstantiate err) (return ())*) fun _ -> next ())
      end
    | NewCommand("defer", ArgEmpty) -> modify (fun (j::js) -> js @ [j]); next ()
    | NewCommand(com, args) when M.mem com env.newcommands ->
      begin try
        comrunner env ((M.find com env.newcommands) env args js);
        next ()
      with err ->
        put js; CommandError(com, (*err (return ())*) fun _ -> next ())
      end
    | NewCommand(com, args) ->
      CommandError(com, (*(toException NoSuchCommand) (return ())*) fun _ -> next ())
  )
