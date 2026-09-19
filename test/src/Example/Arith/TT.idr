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
data Op : Type where
  PLUS  : Op
  MINUS : Op
  TIMES : Op
  EQ    : Op
  LT    : Op
  LTE   : Op
  GT    : Op
  GTE   : Op
  AND   : Op
  OR    : Op
  NOT   : Op
  NEG   : Op

%runElab derive "Op" [Show,Eq]

export
Interpolation Op where
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
  interpolate NEG   = "-"
  interpolate NOT   = "~"

public export
0 BOp : Type
BOp = ByteBounded Op

public export
data Syntax : Type where
  SDef  : ByteBounds -> String -> Syntax
  SSeq  : Skot Syntax BOp -> Syntax -> Syntax
  SBool : ByteBounds -> Bool -> Syntax
  SNat  : ByteBounds -> Nat -> Syntax

%runElab derive "Syntax" [Show,Eq]

export %inline
seq : Skot Syntax BOp -> Syntax -> Syntax
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
  EShunt    : ShuntingErr Op -> Error
  NotInfix  : Op -> Error
  NotPrefix : Op -> Error
  TypeErr   : (exp, fnd : Tpe) -> Error

%runElab derive "Error" [Show,Eq]

export
Interpolation Error where
  interpolate (MNotFound m) = "module not found: \{m}"
  interpolate (QNotFound m) = "name not found: \{m}"
  interpolate (NNotFound m) = "name not found: \{m}"
  interpolate (EShunt x)    = interpolate x
  interpolate (NotInfix x)  = "not an infix operator: \{x}"
  interpolate (NotPrefix x) = "not a prefix operator: \{x}"
  interpolate (TypeErr x y) = "can't unify \{x} (expected) with \{y} (found)"

export %inline
Cast (ShuntingErr Op) Error where cast = EShunt

--------------------------------------------------------------------------------
-- Desugaring
--------------------------------------------------------------------------------

public export
data Term : Type where
  TI    : ByteBounds -> Term -> ByteBounded Op -> Term -> Term
  TP    : ByteBounds -> ByteBounded Op -> Term -> Term
  TDef  : ByteBounds -> String -> Term
  TBool : ByteBounds -> Bool -> Term
  TNat  : ByteBounds -> Nat -> Term

%runElab derive "Term" [Show,Eq]

export
Cast Term ByteBounds where
  cast (TI b _ _ _) = b
  cast (TP b _ _)   = b
  cast (TDef b _)   = b
  cast (TBool b _)  = b
  cast (TNat b _)   = b

ti : Term -> BOp -> Term -> Term
ti x o y = TI (cast x <+> cast y) x o y

tp : BOp -> Term -> Term
tp o y = TP (o.bounds <+> cast y) o y

public export
0 TErr : Type
TErr = BBErr Error

toErr : ShuntingErr BOp -> TErr
toErr (AssocNone bo p) = B (Custom $ EShunt $ AssocNone bo.val p) bo.bounds

shuntTok : Tok Syntax BOp -> Either TErr (Tok Term BOp)

skot : Toks Term BOp -> Skot Syntax BOp -> Either TErr (Skot Term BOp)
skot is [<]     = Right ([<] <>< is)
skot is (si:<i) =
 let Right i2 := shuntTok i | Left x => Left x
  in skot (i2::is) si

export
desugar : Syntax -> Either TErr Term
desugar (SSeq sk s) = Prelude.do
  skt <- skot [] sk
  t   <- desugar s
  mapFst toErr $ shuntingYard ti tp skt t
desugar (SDef b x)  = Right (TDef b x)
desugar (SBool b x) = Right (TBool b x)
desugar (SNat b x)  = Right (TNat b x)

shuntTok (TPre o n) = Right (TPre o n)
shuntTok (TInf t o n a) =
 let Right s := desugar t | Left x => Left x
  in Right (TInf s o n a)

--------------------------------------------------------------------------------
-- Type Theory
--------------------------------------------------------------------------------

public export
0 IType : Tpe -> Type
IType B = Bool
IType I = Integer

public export
data TTOp : List Tpe -> Tpe -> Type where
  T_PLUS  : TTOp [I,I] I
  T_MINUS : TTOp [I,I] I
  T_TIMES : TTOp [I,I] I
  T_EQ    : TTOp [t,t] B
  T_LT    : TTOp [t,t] B
  T_LTE   : TTOp [t,t] B
  T_GT    : TTOp [t,t] B
  T_GTE   : TTOp [t,t] B
  T_AND   : TTOp [B,B] B
  T_OR    : TTOp [B,B] B
  T_NEG   : TTOp [I]   I
  T_NOT   : TTOp [B]   B

%runElab deriveIndexed "TTOp" [Show]

public export
data TT : Tpe -> Type where
  TTFun  : {r : _} -> TTOp ts r -> All TT ts -> TT r
  TTBool : Bool -> TT B
  TTInt  : Integer -> TT I

export
fromValue : {t : _} -> IType t -> TT t
fromValue {t = B} v = TTBool v
fromValue {t = I} v = TTInt v

export
ttpe : TT t -> Singleton t
ttpe (TTFun _ _) = %search
ttpe (TTBool _)  = %search
ttpe (TTInt _)   = %search

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

evalOp : TTOp ts r -> All TT ts -> IType r

export
eval : TT t -> IType t
eval (TTFun x y) = evalOp x y
eval (TTBool x)  = x
eval (TTInt i)   = i

evalOp T_PLUS  [x,y] = eval x + eval y
evalOp T_MINUS [x,y] = eval x - eval y
evalOp T_TIMES [x,y] = eval x * eval y
evalOp T_EQ    [x,y] = let _ := ord x in eval x == eval y
evalOp T_LT    [x,y] = let _ := ord x in eval x <  eval y
evalOp T_LTE   [x,y] = let _ := ord x in eval x <= eval y
evalOp T_GT    [x,y] = let _ := ord x in eval x >  eval y
evalOp T_GTE   [x,y] = let _ := ord x in eval x >= eval y
evalOp T_AND   [x,y] = let _ := ord x in eval x && eval y
evalOp T_OR    [x,y] = let _ := ord x in eval x || eval y
evalOp T_NEG   [x]   = negate (eval x)
evalOp T_NOT   [x]   = not (eval x)
