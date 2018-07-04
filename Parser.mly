%{open FOL open LK open Claire %}
%token FORALL EXIST TOP BOTTOM ARROW OR AND DOT COMMA
%token LPAREN RPAREN LBRACE RBRACE
%token LBRACK PLBRACK TLBRACK ILBRACK NLBRACK RBRACK
%token TILDA NEWLINE COLON SEMI BAR EQ USCORE
%token FUN THEOREM PROOF QED AXIOM CONSTANT
%token PRINT_PROOF ML_FILE IMPORT APPLY NOAPPLY USE INST I CUT
%token ANDL1 ANDL2 ANDR ORL ORR1 ORR2
%token IMPL IMPR BOTTOML TOPR
%token FORALLL FORALLR EXISTL EXISTR
%token WL WR CL CR PL PR PROP EOF
%token <int> NUMBER
%token <string> IDENT STRING HASKELL TVAR
%right ARROW %left AND OR %nonassoc TILDA %right FUN
%start laire %type <Claire.laire> laire
%start decl %type <Claire.decl> decl
%start command %type <Claire.command> command
%start formula %type <FOL.formula> formula
%start term %type <FOL.term> term
%%
laire     : decls                               { Laire $1 }
decls     : /* empty */                         { [] }
          | decl decls                          { $1 :: $2 }
decl      : THEOREM IDENT COLON formula proof   { ThmD($2, $4, $5) }
          | AXIOM IDENT COLON formula           { AxiomD($2, $4) }
          | IMPORT STRING                       { ImportD $2 }
          | PRINT_PROOF                         { PrintProof }
          | CONSTANT IDENT COLON type_          { ConstD($2, $4) }
          | ML_FILE STRING                      { MlFile $2 }
          | IDENT LBRACE arguments RBRACE       { NewDecl($1, $3) }
arguments : /* empty */                         { [] }
          | argument SEMI arguments             { $1 :: $3 }
proof     : /* empty */                         { Proof [] }
          | PROOF commands QED                  { Proof $2 }
commands  : /* empty */                         { [] }
          | command commands                    { $1 :: $2 }
command   : APPLY rule                          { Apply [$2] }
          | APPLY LPAREN rules RPAREN           { Apply $3 }
          | NOAPPLY rule                        { NoApply $2 }
          | USE IDENT pairsExp                  { Use($2, $3) }
          | INST IDENT LBRACK predicate RBRACK  { Inst($2, $4) }
          | IDENT argument                      { NewCommand($1, $2) }
argument  : /* empty */                         { ArgEmpty }
          | PLBRACK predicates RBRACK           { ArgPreds $2 }
          | NLBRACK IDENT COLON type_ RBRACK    { ArgTyped($2, $4) }
          | TLBRACK terms RBRACK                { ArgTerms $2 }
          | ILBRACK identPairs RBRACK           { ArgIdents $2 }
predicates: /* empty */                         { [] }
          | predicate                           { [$1] }
          | predicate COMMA predicates          { $1 :: $3 }
predicate : IDENT FUN predicate                 { PredFun([$1], $3) }
          | LPAREN idents RPAREN FUN predicate  { PredFun($2, $5) }
          | formula                             { PredFml $1 }
idents    : IDENT                               { [$1] }
          | IDENT COMMA idents                  { $1 :: $3 }
identPairs: IDENT pairsExp                      { [($1,$2)] }
          | IDENT pairsExp COMMA identPairs     { ($1,$2) :: $4 }
pairsExp  : /* empty */                         { [] }
          | LBRACE pairs RBRACE                 { $2 }
pairs     : IDENT COLON predicate               { [($1,$3)] }
          | IDENT COLON predicate COMMA pairs   { ($1,$3) :: $5 }
rules     : rule                                { [$1] }
          | rule COMMA rules                    { $1 :: $3 }
rule      : I                                   { I }
          | CUT LBRACK formula RBRACK           { Cut $3 }
          | ANDL1                               { AndL1 }
          | ANDL2                               { AndL2 }
          | ANDR                                { AndR }
          | ORL                                 { OrL }
          | ORR1                                { OrR1 }
          | ORR2                                { OrR2 }
          | IMPL                                { ImpL }
          | IMPR                                { ImpR }
          | BOTTOML                             { BottomL }
          | TOPR                                { TopR }
          | FORALLL LBRACK term RBRACK          { ForallL $3 }
          | FORALLR IDENT                       { ForallR $2 }
          | EXISTL IDENT                        { ExistL $2 }
          | EXISTR LBRACK term RBRACK           { ExistR $3 }
          | WL                                  { WL }
          | WR                                  { WR }
          | CL                                  { CL }
          | CR                                  { CR }
          | PL NUMBER                           { PL $2 }
          | PR NUMBER                           { PR $2 }
formula   : formula ARROW formula               { Then($1, $3) }
          | FORALL IDENT DOT formula            { Forall($2, $4) }
          | EXIST IDENT DOT formula             { Exist($2, $4) }
          | formula OR formula                  { Or($1, $3) }
          | formula AND formula                 { And($1, $3) }
          | TILDA formula                       { neg $2 }
          | TOP                                 { Top }
          | BOTTOM                              { Bottom }
          | LPAREN formula RPAREN               { $2 }
          | IDENT LPAREN terms RPAREN           { Pred($1, $3) }
          | IDENT                               { Pred($1, []) }
terms     : /* empty */                         { [] }
          | term                                { [$1] }
          | term COMMA terms                    { $1 :: $3 }
term      : term LPAREN terms RPAREN            { App($1, $3) }
          | IDENT FUN term                      { Abs([$1], $3) }
          | LPAREN idents RPAREN FUN term       { Abs($2, $5) }
          | LPAREN term RPAREN                  { $2 }
          | IDENT                               { Var $1 }
type_     : PROP                                { Prop }
          | TVAR                                { VarT $1 }
          | IDENT                               { ConT($1, []) }
          | IDENT LPAREN types RPAREN           { ConT($1, $3) }
          | type_ FUN type_                     { ArrT($1, $3) }
          | LPAREN type_ RPAREN                 { $2 }
types     : type_                               { [$1] }
          | type_ COMMA types                   { $1 :: $3 }
