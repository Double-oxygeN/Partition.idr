import Partition
import Data.String

main : IO ()
main = do
  argv <- getArgs

  n <- pure $ index' 1 argv >>= parsePositive
  ls <- pure $ naiveAllParN <$> n

  printLn ls
  printLn $ length <$> ls
