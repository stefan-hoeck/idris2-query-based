module Example.Basic.Query

import Data.ByteString
import Data.Linear.Traverse1
import Data.SortedMap as SM
import Derive.Enum
import public Control.Query

%default total
%language ElabReflection

public export
data TestQ : Type where
  Content  : TestQ
  Lines    : TestQ
  LineMap  : TestQ
  FirstPos : TestQ

%runElab derive "TestQ" [Show,Enum]

public export
0 TestArg : TestQ -> Type
TestArg Content  = String
TestArg Lines    = String
TestArg LineMap  = String
TestArg FirstPos = (String,String)

public export
0 TestRes : TestQ -> Type
TestRes Content  = ByteString
TestRes Lines    = List String
TestRes LineMap  = SortedMap String Nat
TestRes FirstPos = Nat

public export
0 TestC : QTypes
TestC = QT TestQ TestArg TestRes [String]

public export
0 Files : Type
Files = SortedMap String ByteString

export %hint
testQTC : QIface TestC
testQTC =
  QI {
    eqArg   = darrayAuto _ _
  , ordArg  = darrayAuto _ _
  , showArg = darrayAuto _ _
  }

%inline
memo : PrimRunner s TestC
memo = qrun {c = TestC}

inner : Ref s Files -> PrimRunner s TestC
inner r f Content  x t =
 let sm # t := read1 r t
     Just c := lookup x sm | _ => throw1 "File not found: '\{x}'" t
  in R c t
inner _ f Lines    x t =
 let R bs t := memo f Content x t | E e t => E e t
  in R (lines $ ByteString.toString bs) t
inner _ f LineMap  x t =
 let R ls t := memo f Lines x t | E e t => E e t
  in R (SM.fromList $ swap <$> zipWithIndex ls) t
inner _ f FirstPos (y,l) t =
 let R m t  := memo f LineMap y t | E e t => E e t
     Just n := lookup l m         | _ => throw1 "Line not found in '\{y}': '\{l}'" t
  in R n t

public export
record TestEnv (s : Type) where
  constructor TE
  fileContent : String -> ByteString -> F1' s
  testEngine  : FRunner s TestC

fc : Engine s TestC -> Ref s Files -> String -> ByteString -> F1' s
fc e fs f bs t =
 let _ # t := mod1 fs (insert f bs) t
  in e.notify Content f t

export covering
testEngine : F1 s (TestEnv s)
testEngine t =
 let files # t := ref1 {a = Files} empty t
     engi  # t := engine (inner files) t
  in TE (fc engi files) engi.runner # t
