module Example.Arith.Query

import Data.ByteString
import Data.SortedMap
import Derive.Enum
import Example.Arith.Parser
import public Example.Arith.TT
import public Control.Query
import Syntax.E1

%default total
%hide TTImp.Decl
%language ElabReflection

public export
data TestQ : Type where
  Content : TestQ
  Parse   : TestQ
  Env     : TestQ
  Check   : TestQ
  Eval    : TestQ

%runElab derive "TestQ" [Show,Enum]

public export
0 TestArg : TestQ -> Type
TestArg Content  = Module
TestArg Parse    = Module
TestArg Env      = Qualified
TestArg Check    = Qualified
TestArg Eval     = Qualified

public export
0 TestRes : TestQ -> Type
TestRes Content  = ByteString
TestRes Parse    = List Decl
TestRes Env      = (SortedMap String Qualified, Syntax)
TestRes Check    = (t ** TT t)
TestRes Eval     = (t ** IType t)

public export
0 TestC : QTypes
TestC = QT TestQ TestArg TestRes [ParseError Error, Error]

public export
0 Modules : Type
Modules = SortedMap Module ByteString

export %hint
testQTC : QIface TestC
testQTC =
  QI {
    eqArg          = darrayAuto _ _
  , ordArg         = darrayAuto _ _
  , interpolateArg = darrayAuto _ _
  }

%inline
memo : PrimRunner s TestC
memo = qrun {c = TestC}

throw : Ref s (ERunner s TestC) -> TErr -> Module -> E1 s (Errs TestC) a
throw f e m t =
 let R bs t := memo f Content m t | E e t => E e t
  in throw1 (toParseError Virtual (toString bs) e) t

parameters (f  : Ref s (ERunner s TestC))
           (sm : SortedMap String Qualified)

  ti : Term -> Op -> Term -> E1 s (Errs TestC) (QRes TestC Check)

  tp : Op -> Term -> E1 s (Errs TestC) (QRes TestC Check)

  typecheckAs : (t : Tpe) -> Term -> E1 s (Errs TestC) (TT t)

  typecheck : Term -> E1 s (Errs TestC) (t ** TT t)
  typecheck (TI x o y) t = ti x o y t
  typecheck (TP o y)   t = tp o y t
  typecheck (TDef s)   t =
    case lookup s sm of
      Nothing => throw1 (NNotFound s) t
      Just q  => case memo f Eval q t of
        R (_ ** v) t => R (_ ** fromValue v) t
        E e t        => E e t
  typecheck (TBool b)  t = R (_ ** TTBool b) t
  typecheck (TNat n)   t = R (_ ** TTInt (cast n)) t

  typecheckAs tpe x = E1.do
   (tp2 ** tt) <- typecheck x
   case hdecEq tpe tp2 of
     Just0 p  => pure (rewrite p in tt)
     Nothing0 => throw1 (TypeErr tpe tp2)

  op1 : {r : _} -> {tp : _} -> TTOp [tp] r -> Term -> E1 s (Errs TestC) (t ** TT t)
  op1 op x = E1.do
    x2 <- typecheckAs tp x
    pure (r ** TTFun op [x2])

  op2 : {r : _} -> {tp : _} -> TTOp [tp,tp] r -> (x,y : Term) -> E1 s (Errs TestC) (t ** TT t)
  op2 op x y = E1.do
    x2 <- typecheckAs tp x
    y2 <- typecheckAs tp y
    pure (r ** TTFun op [x2,y2])

  opAny : {r : _} -> (forall tp . TTOp [tp,tp] r) -> (x,y : Term) -> E1 s (Errs TestC) (t ** TT t)
  opAny op x y = E1.do
    (tp ** x2) <- typecheck x
    y2         <- typecheckAs tp y
    pure (r ** TTFun op [x2,y2])

  ti x PLUS  y t = op2 T_PLUS  x y t
  ti x MINUS y t = op2 T_MINUS x y t
  ti x TIMES y t = op2 T_TIMES x y t
  ti x EQ    y t = opAny T_EQ  x y t
  ti x LT    y t = opAny T_LT  x y t
  ti x LTE   y t = opAny T_LTE x y t
  ti x GT    y t = opAny T_GT  x y t
  ti x GTE   y t = opAny T_GTE x y t
  ti x AND   y t = op2 T_AND   x y t
  ti x OR    y t = op2 T_OR    x y t
  ti x op    y t = throw1 (NotInfix op) t

  tp NOT   y t = op1 T_NOT y t
  tp NEG   y t = op1 T_NEG y t
  tp op    y t = throw1 (NotPrefix op) t

imports : Ref s (ERunner s TestC) -> SnocList (String,Qualified) -> List Module -> E1 s (Errs TestC) (List (String,Qualified))
imports f sp [] t = R (sp <>> []) t
imports f sp (m::ms) t =
 let R ds t := memo f Parse m t | E e t => E e t
  in imports f (sp <>< mapMaybe (toQualified m) ds) ms t

inner : Ref s Modules -> PrimRunner s TestC
inner r f Content x t =
 let sm # t := read1 r t
     Just c := lookup x sm | _ => throw1 (MNotFound x) t
  in R c t
inner r f Parse x t =
 let R bs t := memo f Content x t | E e t => E e t
  in eitherToE1 (parseBytes decls Virtual bs #) t
inner r f Env x t =
 let R decls t := memo f Parse x.mod t | E e t => E e t
     (ds,Defn _ syn::_) := break (isDefn x.name) decls | _ => throw1 (QNotFound x) t
     ms        := mapMaybe toImport ds
     qs        := mapMaybe (toQualified x.mod) ds
     R es t    := imports f [<] ms t | E e t => E e t
  in R (SortedMap.fromList $ es ++ qs, syn) t
inner r f Check x t =
 let R (sm,syn) t := memo f Env x t | E e t => E e t
     Right trm    := desugar syn | Left e => throw f e x.mod t
  in typecheck f sm trm t
inner r f Eval x t =
 let R (tp ** tt) t := memo f Check x t | E e t => E e t
  in R (tp ** eval tt) t

public export
record TestEnv (s : Type) where
  constructor TE
  moduleContent : Module -> ByteString -> F1' s
  testEngine    : FRunner s TestC

fc : DebugFlag => Engine s TestC -> Ref s Modules -> Module -> ByteString -> F1' s
fc e fs f bs t =
 let _ # t := mod1 fs (insert f bs) t
     _ # t := debugIf1 "module updated: \{f}" t
  in e.notify Content f t

export covering
testEngine : DebugFlag => F1 s (TestEnv s)
testEngine t =
 let files # t := ref1 {a = Modules} empty t
     engi  # t := engine (inner files) t
  in TE (fc engi files) engi.runner # t
