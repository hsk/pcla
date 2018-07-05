{ open Parser }
let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z']
let white = [' ' '\t' '\n' '\r']
rule tokens = parse
  | white+          { tokens lexbuf }
  | "#"[^'\n' '\r']*{ tokens lexbuf }
  | "Forall"        { FORALL }
  | "Exist"         { EXIST }
  | "Top"           { TOP }
  | "Bottom"        { BOTTOM }
  | "==>"           { ARROW }
  | "=>"	          { FUN }
  | "\\/"           { OR }
  | "/\\"           { AND }
  | "."             { DOT }
  | ","             { COMMA }
  | "("             { LPAREN }
  | ")"             { RPAREN }
  | "{"             { LBRACE }
  | "}"             { RBRACE }
  | "["             { LBRACK }
  | "p["            { PLBRACK }
  | "t["            { TLBRACK }
  | "i["            { ILBRACK }
  | "n["            { NLBRACK }
  | "]"             { RBRACK }
  | "~"             { TILDA }
  | ['\n']          { NEWLINE }
  | ":"             { COLON }
  | ";"             { SEMI }
  | "|"             { BAR }
  | "="             { EQ }
  | "_"             { USCORE }
  | "theorem"       { THEOREM }
  | "proof"         { PROOF }
  | "qed"           { QED }
  | "axiom"         { AXIOM }
  | "import"        { IMPORT }
  | "constant"      { CONSTANT }
  | "print_proof"   { PRINT_PROOF }
  | "Ml_file"       { ML_FILE }
  | "apply"         { APPLY }
  | "noapply"       { NOAPPLY }
  | "use"           { USE }
  | "inst"          { INST }
  | "Cut"           { CUT }
  | "I"             { I }
  | "AndL1"         { ANDL1 }
  | "AndL2"         { ANDL2 }
  | "AndR"          { ANDR }
  | "OrL"           { ORL }
  | "OrR1"          { ORR1 }
  | "OrR2"          { ORR2 }
  | "ImpL"          { IMPL }
  | "ImpR"          { IMPR }
  | "BottomL"       { BOTTOML }
  | "TopR"          { TOPR }
  | "ForallL"       { FORALLL }
  | "ForallR"       { FORALLR }
  | "ExistL"        { EXISTL }
  | "ExistR"        { EXISTR }
  | "WL"            { WL }
  | "WR"            { WR }
  | "CL"            { CL }
  | "CR"            { CR }
  | "PL"            { PL }
  | "PR"            { PR }
  | "prop"          { PROP }
  | digit+ as s     { NUMBER (int_of_string s) }
  | '"' ([^ '"']* as s) '"'                  { STRING s }
  | "```" (("``" [^'`'] | _)* as s) "```"    { HASKELL s }
  | "'" alpha (alpha | digit | '_')*   as s  { TVAR s }
  | alpha (alpha | digit | ['_' '\''])* as s { IDENT s }
  | eof             { EOF }
{
open FOL
open LK
open Claire
let pLaire : string -> laire = fun str -> Parser.laire tokens (Lexing.from_string str)
let pDecl : string -> decl = fun str -> Parser.decl tokens (Lexing.from_string str)
let pCommand : string -> command = fun str -> Parser.command tokens (Lexing.from_string str)
let pFormula : string -> formula = fun str -> Parser.formula tokens (Lexing.from_string str)
let pTerm : string -> term = fun str -> Parser.term tokens (Lexing.from_string str)

let readFile f =
  let ic = open_in f in
  let n = in_channel_length ic in
  let s = String.create n in
  really_input ic s 0 n;
  close_in ic;
  s
}