module Control.Query.Types

import Derive.Prelude
import public Control.Monad.Elin
import public Data.DArray
import public Data.Linear.Ref1

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Error Type
--------------------------------------------------------------------------------

||| Key errors, which can be thrown by any query-based system
public export
data QErr : Type where
  ||| A cyclic query was detected
  Cycle   : List String -> QErr

  ||| An initialization error occurred. This is used to define a dummy
  ||| implementation for query runners.
  Unini   : QErr

%runElab derive "QErr" [Show,Eq]

%inline
showCycle : List String -> String
showCycle = fastConcat . intersperse " -> "

export
Interpolation QErr where
  interpolate (Cycle strs)  = "cycle detected: \{showCycle strs}"
  interpolate Unini         = "initialization error"

--------------------------------------------------------------------------------
-- Version
--------------------------------------------------------------------------------

||| Current version in the query system. All nodes have two version
||| numbers: One describing when they last changed their result, the
||| other describing when they were verified the last time.
public export
record Version where
  constructor V
  version : Nat

%runElab derive "Version" [Show,Eq,Ord]

export %inline
inc : Version -> Version
inc (V n) = V (S n)

--------------------------------------------------------------------------------
-- Query Types
--------------------------------------------------------------------------------

||| A query system consists of several related
public export
record QTypes where
  constructor QT

  ||| The type of query, defined as an enumeration
  ||| (it must implement interface `Data.Enum.Enum`)
  0 Query : Type

  ||| The argument type of each kind of query. The key idea of a
  ||| query system is that for each query-argument pair, the result of
  ||| running the query with this argument is memoized in a map.
  |||
  ||| Memoized queries will never be recomputed unless they are invalidated
  ||| because one of their dependencies was invalidated too.
  0 QArg  : Query -> Type

  ||| Result of running a query.
  0 QRes  : Query -> Type

  ||| Types of errors that can be thrown when running queries.
  ||| This should not include `QErr`, as that one will always
  ||| be included (see `Errs`).
  0 Errs_ : List Type

||| Full list of possible error types that can be raised in a
||| given query system.
public export
0 Errs : QTypes -> List Type
Errs c = QErr :: Errs_ c

||| Result of running query `q`.
public export
0 QResult : (c : QTypes) -> (q : Query c) -> Type
QResult c q = Result (Errs c) (QRes c q)

||| Dependent pairing of a query plus its argument.
public export
record QKey (c : QTypes) where
  constructor QK
  query : Query c
  arg   : QArg c query

||| Linear function for running a query. The result is of type
||| `ERes`, which can either be a successful result of type
||| `QRes c q` or an error of type `HSum Errs`.
public export
0 ERunner : (s : Type) -> (c : QTypes) -> Type
ERunner s c = (q : Query c) -> QArg c q -> E1 s (Errs c) (QRes c q)

||| Like `ERunner` but the result is wrapped in an `R1 s (Either x y)`.
public export
0 FRunner : (s : Type) -> (c : QTypes) -> Type
FRunner s c = (q : Query c) -> QArg c q -> F1 s (QResult c q)

||| A primitive query runner.
|||
||| This makes use of a mutable reference holding a query running
||| with memoization capabilities. This is what client code actually
||| has to implement in oder to make use of a query-based system.
|||
||| When running a query, other queries might be invoked to collect
||| the current query's dependences. These other queries must always
||| be invoked via the runner stored in the reference, never by
||| direct recursion.
public export
0 PrimRunner : (s : Type) -> (c : QTypes) -> Type
PrimRunner s c = Ref s (ERunner s c) -> ERunner s c

||| Utilitie for converting an `ERunner` to an `FRunner`
export %inline
frun : ERunner s c -> FRunner s c
frun er q arg t =
  case er q arg t of
    E x t => Left x # t
    R v t => Right v # t

||| Utilitie for converting an `FRunner` to an `ERunner`
export %inline
erun : FRunner s c -> ERunner s c
erun fr q arg t =
  case fr q arg t of
    Left x  # t => E x t
    Right x # t => R x t

||| Utility primitive runner which just invokes the stored runner.
export %inline
qrun : PrimRunner s c
qrun ref q arg t = let f # t := read1 ref t in f q arg t

||| Interface record type holding all the constraints required
||| for running queries.
public export
record QIface (c : QTypes) where
  constructor QI
  {nqueries  : Bits32}
  eqArg      : DArray (Query c) (Eq . QArg c)
  ordArg     : DArray (Query c) (Ord . QArg c)
  showArg    : DArray (Query c) (Show . QArg c)
  {auto qen  : Enum (Query c) nqueries}
  {auto qeq  : Eq (Query c)}
  {auto qord : Ord (Query c)}
  {auto qshw : Show (Query c)}
