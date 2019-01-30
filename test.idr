import Partition
import Data.String

partial
main : IO ()
main = do
  argv <- getArgs

  n <- pure $ index' 1 argv >>= parsePositive
  ls <- pure $ allParN <$> n

  printLn ls
  printLn $ length <$> ls
