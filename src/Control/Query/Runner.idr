module Control.Query.Runner

import Data.SortedMap
import public Control.Query.Types

%default total

--------------------------------------------------------------------------------
-- Query Engine
--------------------------------------------------------------------------------

||| Engine for running queries.
public export
record Engine (s : Type) (c : QTypes) where
  constructor E
  ||| Fully memoized query runner
  runner : FRunner s c

  ||| Facility for external notification that the state of one or several
  ||| nodes in the query graph changed. These are typically root nodes.
  |||
  ||| The most basic example is the content of a relevant file having
  ||| changed.
  notify : (q : Query c) -> QArg c q -> F1' s

||| From a primitive query runner, generates a full-fledged query engine.
export covering
engine : QIface c => PrimRunner s c -> F1 s (Engine s c)

--------------------------------------------------------------------------------
-- In-memory query state and store
--------------------------------------------------------------------------------

record QState (c : QTypes) (q : Query c) where
  constructor QS
  result   : Result (Errs c) (QRes c q)
  changed  : Version
  verified : Version
  deps     : List (QKey c)

0 QMap : (c : QTypes) -> Query c -> Type
QMap c q = SortedMap (QArg c q) (QState c q)

0 QStore : (s : Type) -> (c : QTypes) -> Type
QStore s c = MDArray s (Query c) (QMap c)

emptyMap : QIface c => (q : Query c) -> QMap c q
emptyMap @{QI e o s} q = let ord := at o q in empty

parameters (m       : QStore s c)
           {auto en : Enum (Query c) n}
           (q       : Query c)
           (arg     : QArg c q)
  %inline
  lkp : F1 s (Maybe $ QState c q)
  lkp t = let mp # t := dget m q t in lookup arg mp # t

  %inline
  mem : QState c q -> F1' s
  mem st t = let mp # t := dget m q t in dset m q (insert arg st mp) t

  %inline
  rem : F1' s
  rem t = let mp # t := dget m q t in dset m q (delete arg mp) t

qstore : (0 c : QTypes) -> QIface c => F1 s (QStore s c)
qstore c @{tc} t = let en := tc.qen in mdarray1 (Query c) (QMap c) emptyMap t

--------------------------------------------------------------------------------
-- Runner
--------------------------------------------------------------------------------

parameters (0 c     : QTypes)
           {0 s     : Type}
           {auto en : Enum (Query c) n}
           (curr    : Version)
           (store   : QStore s c)
           (stack   : Ref s (SnocList $ QKey c))
           (qr      : ERunner s c)

  covering
  verifyDeps : Version -> List (QKey c) -> F1 s Bool

  covering
  verify : (q : Query c) -> QArg c q -> QState c q -> F1 s Bool
  verify q arg (QS r c v ds) t =
    case v == curr of
      True  => True # t
      False => case verifyDeps v ds t of
        True  # t =>
         let _ # t := mem store q arg (QS r c curr ds) t
          in True # t
        False # t => let _ # t := rem store q arg t in False # t

  verifyDeps v []               t = True # t
  verifyDeps v (QK q arg :: ks) t =
    case lkp store q arg t of
      Nothing # t => False # t
      Just qs # t => case qs.verified == curr && qs.changed >= v of
        True  => False # t
        False => case verify q arg qs t of
          True  # t => verifyDeps v ks t
          False # t => False # t

  covering %inline
  compute : ERunner s c
  compute q arg t =
   let sk  # t := read1 stack t
       _   # t := write1 stack [<] t
       r   # t := toResult (qr q arg t)
       skr # t := read1 stack t
       _   # t := mem store q arg (QS r curr curr $ skr <>> []) t
       _   # t := write1 stack (sk:<QK q arg) t
    in resultToE1 (r #) t

  covering %inline
  loop : ERunner s c
  loop q arg t =
   case lkp store q arg t of
     Nothing  # t => compute q arg t
     Just qst # t => case verify q arg qst t of
       False # t => compute q arg t
       True  # t => resultToE1 (qst.result #) t

%inline
unini : (0 c : QTypes) -> ERunner s c
unini c _ _ = throw1 Unini

covering %inline
runner : Enum (Query c) n => Ref s Version -> QStore s c -> PrimRunner s c -> FRunner s c
runner ref st prim q arg t =
 let v      # t := read1 ref t
     sk     # t := ref1 {a = SnocList $ QKey c} [<] t
     runref # t := ref1 (unini c) t
     qr         := prim runref
     _      # t := write1 runref (loop c v st sk qr) t
  in frun (loop c v st sk qr) q arg t

%inline
ntfy : Enum (Query c) n => Ref s Version -> QStore s c -> (q : Query c) -> QArg c q -> F1' s
ntfy v st q arg t =
 let _ # t := mod1 v inc t
  in rem st q arg t

engine @{tc} prim  t =
 let en         := tc.qen
     vers   # t := ref1 (V 0) t
     str    # t := qstore c t
  in E (runner vers str prim) (ntfy vers str) # t
