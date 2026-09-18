module Example.Arith.Test

import Data.ByteString
import Example.Arith.Query
import Syntax.T1

%default total

factorials : ByteString
factorials =
  """
  fact0 = 1;
  fact1 = 1 * fact0;
  fact2 = 2 * fact1;
  fact3 = 3 * fact2;
  fact4 = 4 * fact3;
  fact5 = 5 * fact4;
  """

factorials2 : ByteString
factorials2 = factorials <+> "fact6 = 6 * fact5;"

examples : ByteString
examples =
  """
  import Factorials

  test1 = fact5 > fact4 && fact4 > fact3;

  test2 = ~test1;

  test3 = fact6 * fact5;
  """

logVal : F1 World (QResult TestC Eval) -> IO1 ()
logVal f t =
  case f t of
    Left xs # t => debug1 (interpolate xs) t
    Right p # t => debug1 (interpolate p) t

covering
example1 : IO1 ()
example1 = T1.do
  TE fc run <- testEngine
  fc "Factorials" factorials
  fc "Examples" examples
  logVal (run Eval $ Q "Factorials" "fact5")
  logVal (run Eval $ Q "Factorials" "fact6")
  logVal (run Eval $ Q "Examples" "test1")
  logVal (run Eval $ Q "Examples" "test2")
  logVal (run Eval $ Q "Examples" "test3")
  fc "Factorials" factorials2
  logVal (run Eval $ Q "Factorials" "fact6")
  logVal (run Eval $ Q "Examples" "test3")

export covering
runArith : IO ()
runArith = runIO example1
