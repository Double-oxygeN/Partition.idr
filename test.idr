import Partition
import Data.PosNat

main : IO ()
main = do
  case (mkPar [(p 6), (p 5), (p 5), (p 2), (p 1), (p 1), (p 1)]) of
    Just l =>
      print $ size l

    Nothing =>
      print "error"
