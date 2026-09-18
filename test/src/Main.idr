module Main

import Example.Arith.Test
import Example.Basic.Test

%default total

main : IO ()
main = runBasic >> runArith
