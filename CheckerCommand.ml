open FOL
open LK
open Claire
open Env
open Typecheck
exception GoalError of rule * judgement list

let judge : env -> rule list -> judgement list -> judgement list =
  fun thms rs js ->
    let rec deleteAt k xs = match k,xs with
      | k,[] -> []
      | 0,x::xs -> xs
      | k,x::xs -> x::deleteAt (k-1) xs
    in
    let go = fun j r -> match j,r with
      | I, Judgement(assms, props) :: js when List.length assms = 1 && assms = props -> js
      | Cut fml, Judgement(assms, props) :: js -> Judgement(assms,(fml::props)) :: Judgement((fml::assms), props) :: js
      | AndL1, Judgement((And(fa, fb)::assms), props) :: js -> Judgement((fa::assms), props) :: js
      | AndL2, Judgement((And(fa, fb)::assms), props) :: js -> Judgement((fb::assms), props) :: js
      | AndR, Judgement(assms, (And(fa, fb)::props)) :: js -> Judgement(assms,(fa::props)) :: Judgement(assms,(fb::props)) :: js
      | OrL, Judgement((Or(fa,fb)::assms),props) :: js -> Judgement((fa::assms), props) :: Judgement((fb::assms), props) :: js
      | OrR1, Judgement(assms, (Or(fa,fb)::props)) :: js -> Judgement(assms,(fa::props)) :: js
      | OrR2, Judgement(assms, (Or(fa,fb)::props)) :: js -> Judgement(assms,(fb::props)) :: js
      | ImpL, Judgement((Then(fa, fb)::assms), props) :: js -> Judgement(assms,(fa::props)) :: Judgement((fb::assms), props) :: js
      | ImpR, Judgement(assms, (Then(fa, fb)::props)) :: js -> Judgement((fa::assms), (fb::props)) :: js
      | BottomL, Judgement((Bottom::assms), props) :: js -> js
      | TopR, Judgement(assms, (Top::props)) :: js -> js
      | ForallL t, Judgement((Forall(x, fml)::assms), props) :: js -> Judgement((substTerm x t fml::assms), props) :: js
      | ForallR y, Judgement(assms, (Forall(x, fml)::props)) :: js -> Judgement(assms,(substTerm x (Var y) fml::props)) :: js
      | ExistL y, Judgement((Exist(x, fml)::assms), props) :: js -> Judgement((substTerm x (Var y) fml::assms), props) :: js
      | ExistR t, Judgement(assms, (Exist(x, fml)::props)) :: js -> Judgement(assms,(substTerm x t fml::props)) :: js
  
      | WL, Judgement((_::assms), props) :: js -> Judgement(assms, props) :: js
      | WR, Judgement(assms, (_::props)) :: js -> Judgement(assms, props) :: js
      | CL, Judgement((fml::assms), props) :: js -> Judgement((fml::fml::assms), props) :: js
      | CR, Judgement(assms, (fml::props)) :: js -> Judgement(assms, (fml::fml::props)) :: js
      | PL k, Judgement(assms, props) :: js when k < List.length assms -> Judgement((List.nth assms k :: deleteAt k assms), props) :: js
      | PR k, Judgement(assms, props) :: js when k < List.length props -> Judgement(assms, (List.nth props k :: deleteAt k props)) :: js
      | r, js -> raise (GoalError (r,js))
    in
    List.fold_left (fun m r -> go r m) js rs
(*--*)

type comSuspender =
  | ComAwait of (command -> unit -> comSuspender)
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
    | ComAwait k ->
      begin match cs with
      | [] -> ()
      | c::cs' -> go (k c) cs'
      end
    | CommandError(s, err) -> failwith s
    | ComReturn -> ()
  in
  go (commandM env) cs
and commandM : env -> unit -> comSuspender =
fun env () ->
  ComAwait(fun com ()->
  let insts fml pairs =
    List.fold_left (fun f (idt,pred) -> substPred ("?"^idt) pred f) fml pairs
  in
  let next () =
    if get () = [] then ComReturn else commandM env ()
  in
  let js = get() in
  begin match com with
    | Apply rs ->
      begin try
        let js = get () in
        let js' = judge env rs js in
        put js';
        let js = get () in
        next()
      with GoalError (r,js') ->
        CommandError("apply", (* (toException $ CannotApply r js') (return ()) *) fun _ ->
          commandM env; next ())
      end
    | NoApply r ->
      begin try
        let js = get () in
        let js' = judge env [r] js in
        next ()
      with GoalError (r,js') ->
          CommandError("noapply", (*(toException $ CannotApply r js') (return ()) *) fun _ ->
          commandM env; next ())
      end
    | Use(idx, pairs) when M.mem idx env.thms ->
      begin try
        let fml = M.find idx env.thms in
        let r = insts fml pairs in
        modify (fun (Judgement(assms, props) :: js) -> Judgement (r::assms, props) :: js);
        next ()
      with err -> CommandError("inst", (*(toException $ CannotInstantiate err) (return ())*) fun _ -> next())
      end
    | Use(idx, pairs) ->
      CommandError("use", (*(toException $ NoSuchTheorem idx) (return ())*) fun _ -> next())
    | Inst(idt, pred) ->
      let js = get () in
      begin match js with
        | [] -> CommandError("inst", (*(toException (error "empty judgement" :: ErrorCall)) (return ())*) fun _ -> next())
        | Judgement(assm::assms, props) :: js' ->
          begin try
            let r = substPred ("?"^idt) pred assm in
            put (Judgement(r::assms, props) :: js');
            next ()
          with err -> CommandError("inst", (*(toException $ CannotInstantiate err) (return ())*) fun _ -> next ())
          end
        (*| j :: _ -> failwith (Printf.sprintf "inst user error error %s" (show_judgement j ))*)
        
      end
    | NewCommand("defer", ArgEmpty) -> modify (fun (j::js) -> js @ [j]); next ()
    | NewCommand(com, args) when M.mem com env.newcommands ->
      let js = get () in
      begin try
        comrunner env ((M.find com env.newcommands) env args js);
        next ()
      with err ->
        put js; CommandError(com, (*err (return ())*) fun _ -> next ())
      end
    | NewCommand(com, args) ->
      CommandError(com, (*(toException NoSuchCommand) (return ())*) fun _ -> next ())
  end
  )
