module Example.Arith.TT

import Derive.HDecEq
import Derive.Prelude
import public Data.Singleton
import public Text.ILex
import public Text.ILex.Shunting

%default total
%language ElabReflection
%hide TTImp.Decl

--------------------------------------------------------------------------------
-- Surface Language
--------------------------------------------------------------------------------

public export
data Tpe = B | I

%runElab derive "Tpe" [Show,Eq,HDecEq]

export
Interpolation Tpe where
  interpolate B = "Bool"
  interpolate I = "Integer"

public export
record Module where
  constructor M
  name : String

%runElab derive "Module" [Show,Eq,Ord,FromString]

export %inline
Interpolation Module where interpolate = name

public export
record Qualified where
  constructor Q
  mod  : Module
  name : String

%runElab derive "Qualified" [Show,Eq,Ord]

public export
data IOp : Type where
  PLUS  : IOp
  MINUS : IOp
  TIMES : IOp
  EQ    : IOp
  LT    : IOp
  LTE   : IOp
  GT    : IOp
  GTE   : IOp
  AND   : IOp
  OR    : IOp

%runElab derive "IOp" [Show,Eq]

export
Interpolation IOp where
  interpolate PLUS  = "+"
  interpolate MINUS = "-"
  interpolate TIMES = "*"
  interpolate EQ    = "=="
  interpolate LT    = "<"
  interpolate LTE   = "<="
  interpolate GT    = ">"
  interpolate GTE   = ">="
  interpolate AND   = "&&"
  interpolate OR    = "||"

public export
data POp : Type where
  NOT   : POp
  NEG   : POp

%runElab derive "POp" [Show,Eq]

export
Interpolation POp where
  interpolate NEG   = "-"
  interpolate NOT   = "~"

public export
data Syntax : Type where
  SDef  : ByteBounds -> String -> Syntax
  SSeq  : Skot Syntax POp IOp -> Syntax -> Syntax
  SBool : ByteBounds -> Bool -> Syntax
  SNat  : ByteBounds -> Nat -> Syntax
  SPar  : ByteBounds -> Syntax -> Syntax

%runElab derive "Syntax" [Show,Eq]

export %inline
seq : Skot Syntax POp IOp -> Syntax -> Syntax
seq [<] x = x
seq sp  x = SSeq sp x

public export
data Decl : Type where
  Import : ByteBounded Module -> Decl
  Defn   : ByteBounded String -> Syntax -> Decl

%runElab derive "Decl" [Show,Eq]

export
isDefn : String -> Decl -> Bool
isDefn n (Defn x _) = n == x.val
isDefn n _          = False

export
toImport : Decl -> Maybe (ByteBounded Module)
toImport (Import n) = Just n
toImport _          = Nothing

export
toQualified : Module -> Decl -> Maybe (String, Qualified)
toQualified m (Defn n _) = Just (n.val, Q m n.val)
toQualified _ _          = Nothing

--------------------------------------------------------------------------------
-- Error Type
--------------------------------------------------------------------------------

export %inline
Interpolation Qualified where interpolate (Q m n) = "\{m}.\{n}"

public export
data Error : Type where
  MNotFound : Module -> Error
  QNotFound : Qualified -> Error
  NNotFound : String -> Error
  EShunt    : ShuntingErr IOp -> Error
  TypeErr   : (exp, fnd : Tpe) -> Error

%runElab derive "Error" [Show,Eq]

export %inline
Cast (ShuntingErr IOp) Error where cast = EShunt

export
Interpolation Error where
  interpolate (MNotFound m) = "module not found: \{m}"
  interpolate (QNotFound m) = "name not found: \{m}"
  interpolate (NNotFound m) = "name not found: \{m}"
  interpolate (EShunt x)    = interpolate x
  interpolate (TypeErr x y) = "can't unify \{x} (expected) with \{y} (found)"

--------------------------------------------------------------------------------
-- Desugaring
--------------------------------------------------------------------------------

public export
data Term : Type where
  TI    : ByteBounds -> Term -> IOp -> Term -> Term
  TP    : ByteBounds -> POp -> Term -> Term
  TDef  : ByteBounds -> String -> Term
  TBool : ByteBounds -> Bool -> Term
  TNat  : ByteBounds -> Nat -> Term
  TPar  : ByteBounds -> Term -> Term

%runElab derive "Term" [Show,Eq]

export
Cast Term ByteBounds where
  cast (TI b _ _ _) = b
  cast (TP b _ _)   = b
  cast (TDef b _)   = b
  cast (TBool b _)  = b
  cast (TNat b _)   = b
  cast (TPar _ x)   = cast x

outer : Term -> ByteBounds
outer (TPar b _) = b
outer t          = cast t

ti : Term -> ByteBounded IOp -> Term -> Term
ti x o y = TI (outer x <+> outer y) x o.val y

tp : ByteBounded POp -> Term -> Term
tp o y = TP (o.bounds <+> outer y) o.val y

public export
0 TErr : Type
TErr = BBErr Error

shuntTok : Tok Syntax POp IOp -> Either TErr (Tok Term POp IOp)

skot : Toks Term POp IOp -> Skot Syntax POp IOp -> Either TErr (Skot Term POp IOp)
skot is [<]     = Right ([<] <>< is)
skot is (si:<i) =
 let Right i2 := shuntTok i | Left x => Left x
  in skot (i2::is) si

export
desugar : Syntax -> Either TErr Term
desugar (SSeq sk s) = Prelude.do
  skt <- skot [] sk
  t   <- desugar s
  shuntingYard ti tp skt t
desugar (SDef b x)  = Right (TDef b x)
desugar (SBool b x) = Right (TBool b x)
desugar (SNat b x)  = Right (TNat b x)
desugar (SPar b x)  = TPar b <$> desugar x

shuntTok (TPre o n) = Right (TPre o n)
shuntTok (TInf t o n a) = (\s => TInf s o n a) <$> desugar t

--------------------------------------------------------------------------------
-- Type Theory
--------------------------------------------------------------------------------

public export
0 IType : Tpe -> Type
IType B = Bool
IType I = Integer

public export
data TTIOp : Tpe -> Tpe -> Type where
  T_PLUS  : TTIOp I I
  T_MINUS : TTIOp I I
  T_TIMES : TTIOp I I
  T_EQ    : TTIOp t B
  T_LT    : TTIOp t B
  T_LTE   : TTIOp t B
  T_GT    : TTIOp t B
  T_GTE   : TTIOp t B
  T_AND   : TTIOp B B
  T_OR    : TTIOp B B

%runElab deriveIndexed "TTIOp" [Show]

public export
data TTPOp : Tpe -> Type where
  T_NEG   : TTPOp I
  T_NOT   : TTPOp B

%runElab deriveIndexed "TTPOp" [Show]

public export
data TT : Tpe -> Type where
  TTI    : {r : _} -> TT t -> TTIOp t r -> TT t -> TT r
  TTP    : {r : _} -> TTPOp r -> TT r -> TT r
  TTBool : Bool -> TT B
  TTInt  : Integer -> TT I

export
fromValue : {t : _} -> IType t -> TT t
fromValue {t = B} v = TTBool v
fromValue {t = I} v = TTInt v

export
ttpe : TT t -> Singleton t
ttpe (TTI {})   = %search
ttpe (TTP {})   = %search
ttpe (TTBool _) = %search
ttpe (TTInt _)  = %search

export
Interpolation (t ** IType t) where
  interpolate (B ** v) = "Bool: \{show v}"
  interpolate (I ** v) = "Integer: \{show v}"

--------------------------------------------------------------------------------
-- Evaluation
--------------------------------------------------------------------------------

export
ord : TT t -> Ord (IType t)
ord x =
  case ttpe x of
    Val B => %search
    Val I => %search

evalPre : TTPOp r -> TT r -> IType r

evalInf : TT t -> TTIOp t r -> TT t -> IType r

export
eval : TT t -> IType t
eval (TTI x o y) = evalInf x o y
eval (TTP o y)   = evalPre o y
eval (TTBool x)  = x
eval (TTInt i)   = i

evalInf x T_PLUS  y = eval x + eval y
evalInf x T_MINUS y = eval x - eval y
evalInf x T_TIMES y = eval x * eval y
evalInf x T_EQ    y = let _ := ord x in eval x == eval y
evalInf x T_LT    y = let _ := ord x in eval x <  eval y
evalInf x T_LTE   y = let _ := ord x in eval x <= eval y
evalInf x T_GT    y = let _ := ord x in eval x >  eval y
evalInf x T_GTE   y = let _ := ord x in eval x >= eval y
evalInf x T_AND   y = let _ := ord x in eval x && eval y
evalInf x T_OR    y = let _ := ord x in eval x || eval y

evalPre T_NEG   x   = negate (eval x)
evalPre T_NOT   x   = not (eval x)
