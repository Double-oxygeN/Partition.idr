module Partition

%default total
%access export

(>=) : Nat -> Nat -> Type
(>=) = Nat.GTE

public export
data IsDecreasing : List Nat -> Type where
  DecEmpty : IsDecreasing Nil
  DecSingle : (x: Nat) -> IsDecreasing [S x]
  DecMany :
    (x, y: Nat) -> (ys: List Nat) ->
    x >= y -> IsDecreasing (y :: ys) ->
    IsDecreasing (x :: y :: ys)

public export
data Par : Type where
  MkPar : (ls: List Nat) -> IsDecreasing ls -> Par

Show Par where
  show (MkPar ls _) = "(" ++ join ls "," ++ ")" where
    join : Show a => List a -> String -> String
    join Nil _ = ""
    join (x :: Nil) _ = show x
    join (x :: y :: ys) sep = show x ++ sep ++ join (y :: ys) sep

public export
data ParUpper : Nat -> Type where
  MkParUpper : (k: Nat) -> (ls: List Nat) -> IsDecreasing (k :: ls) -> ParUpper k

forgetUpper : ParUpper k -> Par
forgetUpper (MkParUpper k Nil _) = MkPar Nil DecEmpty
forgetUpper (MkParUpper k _ (DecMany _ x xs _ proofXXsIsDec)) = MkPar (x :: xs) proofXXsIsDec

succDec : IsDecreasing (x :: xs) -> IsDecreasing (S x :: xs)
succDec (DecSingle x) = DecSingle (S x)
succDec (DecMany x y ys proofXGteY proofYYsIsDec) =
  DecMany (S x) y ys (lteSuccRight proofXGteY) proofYYsIsDec

parUpperKIsParUpperSuccK : ParUpper k -> ParUpper (S k)
parUpperKIsParUpperSuccK (MkParUpper k ls proofKLsIsDec) =
  MkParUpper (S k) ls (succDec proofKLsIsDec)

parUpperCons : (k1: Nat) -> (S k1) >= k2 -> ParUpper k2 -> ParUpper (S k1)
parUpperCons k1 proofSuccK1GteK2 (MkParUpper (S k2') Nil (DecSingle k2')) =
  MkParUpper (S k1) [S k1] (DecMany (S k1) (S k1) Nil lteRefl (DecSingle k1))
parUpperCons k1 proofSuccK1GteK2 (MkParUpper k2 _ (DecMany _ y ys proofK2GteY proofYYsIsDec)) =
  MkParUpper (S k1) (S k1 :: y :: ys)
    (DecMany (S k1) (S k1) (y :: ys) lteRefl
      (DecMany (S k1) y ys (lteTransitive proofK2GteY proofSuccK1GteK2) proofYYsIsDec))

allParNUpper : (k : Nat) -> Nat -> List (ParUpper k)
allParNUpper Z _ = Nil
allParNUpper (S k) Z = [MkParUpper (S k) Nil (DecSingle k)]
allParNUpper (S k) n with (isLTE (S k) n)
  | No _ =
    parUpperKIsParUpperSuccK <$> allParNUpper k n
  | Yes _ =
    ((parUpperCons k lteRefl) <$> allParNUpper (S k) (assert_smaller n (n `minus` (S k)))) ++
    (parUpperKIsParUpperSuccK <$> allParNUpper k n)

allParN : Nat -> List Par
allParN Z = [MkPar Nil DecEmpty]
allParN n = forgetUpper <$> allParNUpper n n

