module Example.Arith.Parser

import Example.Arith.TT
import Syntax.T1
import Text.ILex.State.Derive
import Text.ILex.State.Streaming

%default total
%hide Data.Linear.(.)
%hide TTImp.Decl
%language ElabReflection

%runElab deriveParserState "Lexers" "Lexer"
  ["TOP","TERM","IMPORT","INFIX","EQUAL","ERR"]

data STACK : Type where
  Top  : STACK
  Def  : ByteBounded String -> STACK
  SeqT : STACK -> Skot Syntax BPOp BIOp -> Syntax -> STACK
  Seq  : STACK -> Skot Syntax BPOp BIOp -> STACK
  Open : STACK -> BytePos -> STACK

0 ST : Type -> Type
ST = State Error STACK Decl Lexers

parameters {auto sk : ST q}

  putTerm : Syntax -> STACK -> F1 q Lexer
  putTerm trm (Seq p sx) = putStackAs (SeqT p sx trm) INFIX
  putTerm trm p          = putStackAs (SeqT p [<] trm) INFIX

  %inline
  onTerm : (ByteBounds -> Syntax) -> F1 q Lexer
  onTerm x = boundsWithStack $ putTerm . x

  onInfix : IOp -> Nat -> Assoc -> F1 q Lexer
  onInfix o n a =
    bounds >>= \b => withStack $ \case
      SeqT p st t => putStackAs (Seq p $ st:<TInf t (B o b) n a) TERM
      _             => failUnexpected [] ERR

  onPrefix : POp -> Nat -> F1 q Lexer
  onPrefix o n = T1.do
    b <- bounds
    withStack $ \case
      Seq p st => putStackAs (Seq p $ st:<TPre (B o b) n) TERM
      p        => putStackAs (Seq p [<TPre (B o b) n]) TERM

  onClose : F1 q Lexer
  onClose =
    withStack $ \case
      SeqT (Open p _) st x => putTerm (seq st x) p
      _                    => failUnexpected [] ERR

  onSemi : F1 q Lexer
  onSemi =
    withStack $ \case
      SeqT (Def n) st t => pushValue (Defn n $ seq st t) Top TOP
      _                 => failUnexpected [] ERR

  %inline
  onImport : String -> ByteBounds -> F1 q Lexer
  onImport s b =
    getStack >>= \case
      Top => pushValue (Import (B (M s) b)) Top TOP
      _   => failUnexpected [] ERR

linecomment : RExp True
linecomment = "--" >> star dot

spaced : Lexer -> Steps q Lexers ST -> Entry Lexers (DFA q Lexers ST)
spaced x ss = E x $ dfa $ jsonSpaced $ ignore linecomment :: ss

identchar : RExp True
identchar = alphaNum <|> '_' <|> '\''

ident : RExp True
ident = alpha >> star identchar

ptrans : Lex1 q Lexers ST
ptrans =
  lex1
    [ spaced TERM
        [ bytes decimal (onTerm . flip SNat . cast . decimal)
        , step "true" (onTerm $ flip SBool True)
        , step "false" (onTerm $ flip SBool False)
        , step "-" (onPrefix NEG 11)
        , step "~" (onPrefix NOT 11)
        , step '(' $ posModStack ST Open TERM
        , string ident (onTerm . flip SDef)
        ]
    , spaced INFIX
        [ step ')' onClose
        , step ';' onSemi
        , step "+"  $ onInfix PLUS 8 InfixL
        , step "-"  $ onInfix MINUS 8 InfixL
        , step "*"  $ onInfix TIMES 9 InfixL
        , step "==" $ onInfix EQ 6 None
        , step ">"  $ onInfix GT 6 None
        , step "<"  $ onInfix LT 6 None
        , step ">=" $ onInfix GTE 6 None
        , step "<=" $ onInfix LTE 6 None
        , step "&&" $ onInfix AND 5 InfixR
        , step "||" $ onInfix OR 4 InfixR
        ]
      , spaced TOP
          [ step' "import" IMPORT
          , string ident $ \s => bounded' s >>= \x => putStackAs (Def x) EQUAL
          ]
      , spaced IMPORT [string ident $ \s => bounds >>= onImport s]
      , spaced EQUAL [step' '=' TERM]
    ]

perr : Arr32 Lexers (ST q -> F1 q TErr)
perr = errs []

peoi : Lexer -> ST q -> F1 q (Either TErr $ List Decl)
peoi st sk t =
 let Top # t := getStack t | _ # t => arrFail ST perr st sk t
  in values sk t

export
decls : P1 q TErr (List Decl)
decls = P TOP (init ERR Top) ptrans valuesChunk perr peoi
