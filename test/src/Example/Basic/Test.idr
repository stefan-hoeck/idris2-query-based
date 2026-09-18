module Example.Basic.Test

import Data.ByteString
import Example.Basic.Query
import Syntax.T1
import System

%default total

covering
example1 : DebugFlag => Nat -> IO1 ()
example1 n = T1.do
  TE fc run <- testEngine
  fc "Source1" "hello\nworld\n\nthis is\na test!\n\n"
  forN n $ T1.do
    _ <- run FirstPos ("Source1", "hello")
    pure ()

export covering
runBasic : IO ()
runBasic = Prelude.do
  let df := NoDebugging
  [_,n] <- getArgs | _ => runIO (example1 100)
  runIO (example1 $ cast n)
