{-
  Copyright 2018 Double-oxygeN

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

      http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-}

module Partition

%default total
%access export

-- define decreasing rule
public export
(>=) : Nat -> Nat -> Type
(>=) = GTE

public export
data IsDecreasing : List Nat -> Type where
  DecEmpty :
    IsDecreasing Nil

  DecSingle :
    (a: Nat) -> a >= 1 ->
    IsDecreasing (a :: Nil)

  DecMany :
    (a1: Nat) -> (a2: Nat) -> (ax: List Nat) ->
    a1 >= a2 -> IsDecreasing (a2 :: ax) ->
    IsDecreasing (a1 :: a2 :: ax)

-- some theorems

succDec : IsDecreasing (x :: xs) -> IsDecreasing ((S x) :: xs)
succDec (DecSingle x proofXIsPositive) = DecSingle (S x) (lteSuccRight proofXIsPositive)
succDec (DecMany x y ys proofXGteY proofYYsIsDec) = DecMany (S x) y ys (lteSuccRight proofXGteY) proofYYsIsDec

-- define partition
namespace Partition
  public export
  data Par : Type where
    MkPar : (ls: List Nat) -> IsDecreasing ls -> Par

  ParNil : Par
  ParNil = MkPar Nil DecEmpty

  -- partition utility functions
  toList : Par -> List Nat
  toList (MkPar ls _) = ls

  index : (n: Nat) -> (l: Par) -> {auto ok: InBounds n (toList l)} -> Nat
  index n l = Prelude.List.index n (Partition.toList l)

  length : Par -> Nat
  length l = length $ toList l

  multiplicity : Nat -> Par -> Nat
  multiplicity e l = length $ elemIndices e (toList l)

  tail : Par -> Par
  tail (MkPar Nil _) = ParNil
  tail (MkPar (x :: Nil) _) = ParNil
  tail (MkPar (x :: y :: ys) (DecMany x y ys _ proofYYsIsDec)) = (MkPar (y :: ys) proofYYsIsDec)

  sizePar : Par -> Nat
  sizePar (MkPar Nil _) = Z
  sizePar (MkPar (x :: Nil) (DecSingle _ _)) = x
  sizePar (MkPar (x :: y :: ys) (DecMany x y ys proofXGteY proofYYsIsDec)) =
    x + sizePar (assert_smaller (MkPar (x :: y :: ys) (DecMany x y ys proofXGteY proofYYsIsDec)) (MkPar (y :: ys) proofYYsIsDec))

Show Par where
  show l = "(" ++ (join "," (toList l)) ++ ")"
  where
    join : (Show a) => String -> List a -> String
    join _ Nil = ""
    join _ (x :: Nil) = show x
    join s (x :: xs) = (show x) ++ s ++ (join s xs)

-- define partition of size N
public export
data IsSize : Nat -> Par -> Type where
  MkIsSize : (l: Par) -> IsSize (sizePar l) l

public export
data ParN : Nat -> Type where
  MkParN : (l: Par) -> IsSize n l -> ParN n

-- partition with limit
data ParUpper : Nat -> Type where
  MkParUpper : (k: Nat) -> (ls: List Nat) -> IsDecreasing (k :: ls) -> ParUpper k

forgetUpper : ParUpper k -> Par
forgetUpper (MkParUpper k Nil _) = ParNil
forgetUpper (MkParUpper k _ (DecMany _ x xs _ proofXXsIsDec)) = MkPar (x :: xs) proofXXsIsDec

parUpperKIsParUpperSuccK : ParUpper k -> ParUpper (S k)
parUpperKIsParUpperSuccK (MkParUpper k ls proofKLsIsDec) =
  MkParUpper (S k) ls (succDec proofKLsIsDec)

parUpperCons : (k1: Nat) -> k1 >= k2 -> ParUpper k2 -> ParUpper k1
parUpperCons k1 proofK1GteK2 (MkParUpper k2 ls proofK2LsIsDec) =
  case proofK2LsIsDec of
    DecSingle _ proofK2IsPos => MkParUpper k1 [k1] (DecMany k1 k1 [] lteRefl (DecSingle k1 (lteTransitive proofK2IsPos proofK1GteK2)))
    DecMany _ y ys proofK2GteY proofYYsIsDec => MkParUpper k1 (k1 :: y :: ys) (DecMany k1 k1 (y :: ys) lteRefl (DecMany k1 y ys (lteTransitive proofK2GteY proofK1GteK2) proofYYsIsDec))

-- get all Par(N)
naiveAllParNUpper : (k: Nat) -> Nat -> List (ParUpper k)
naiveAllParNUpper Z _ = Nil
naiveAllParNUpper (S k) Z = (MkParUpper (S k) Nil (DecSingle (S k) (LTESucc LTEZero))) :: Nil
naiveAllParNUpper (S k) n with ((S k) <= n)
  | False = parUpperKIsParUpperSuccK <$> naiveAllParNUpper k n
  | True  = ((parUpperCons (S k) lteRefl) <$> naiveAllParNUpper (S k) (assert_smaller n (n `minus` (S k)))) ++ (parUpperKIsParUpperSuccK <$> (naiveAllParNUpper k n))

naiveAllParN : Nat -> List Par
naiveAllParN Z = ParNil :: Nil
naiveAllParN n = forgetUpper <$> naiveAllParNUpper n n

lemma1 : IsSize Z ParNil
lemma1 = MkIsSize ParNil

lemma2 : (n: Nat) -> IsSize (S n) (MkPar [S n] (DecSingle (S n) (LTESucc LTEZero)))
lemma2 n = MkIsSize (MkPar [S n] (DecSingle (S n) (LTESucc LTEZero)))

lemma3 : (k: Nat) -> (n: Nat) -> (proofKGteSuccN: k >= S n) ->
  IsSize (k + S n) (MkPar [k, S n] (DecMany k (S n) Nil proofKGteSuccN (DecSingle (S n) (LTESucc LTEZero))))
lemma3 k n proofKGteSuccN = MkIsSize (MkPar [k, S n] (DecMany k (S n) Nil proofKGteSuccN (DecSingle (S n) (LTESucc LTEZero))))

lemma4 : (k: Nat) -> (x1: Nat) -> (x2: Nat) -> (xs: List Nat) ->
  IsSize n (MkPar (x1 :: x2 :: xs) (DecMany x1 x2 xs proofX1GteX2 proofX2XsIsDec)) -> (proofKGteX1: k >= x1) ->
  IsSize (k + n) (MkPar (k :: x1 :: x2 :: xs) (DecMany k x1 (x2 :: xs) proofKGteX1 (DecMany x1 x2 xs proofX1GteX2 proofX2XsIsDec)))
lemma4 k x1 x2 xs (MkIsSize (MkPar (x1 :: x2 :: xs) (DecMany x1 x2 xs proofX1GteX2 proofX2XsIsDec))) proofKGteX1 =
  MkIsSize (MkPar (k :: x1 :: x2 :: xs) (DecMany k x1 (x2 :: xs) proofKGteX1 (DecMany x1 x2 xs proofX1GteX2 proofX2XsIsDec)))

lemma5 : IsDecreasing (k :: ls) -> Par
lemma5 (DecSingle k _) = ParNil
lemma5 (DecMany k x xs _ proofXXsIsDec) = MkPar (x :: xs) proofXXsIsDec

data ParNUpper : Nat -> Nat -> Type where
  MkParNUpper :
    (k: Nat) -> (ls: List Nat) -> (proofKLsIsDec: IsDecreasing (k :: ls)) ->
    IsSize n (lemma5 proofKLsIsDec) -> ParNUpper k n

forgetUpper' : ParNUpper k n -> ParN n
forgetUpper' (MkParNUpper k ls proofKLsIsDec proofLsIsSizeN) = MkParN (lemma5 proofKLsIsDec) proofLsIsSizeN

lemma6 : (proofKLsIsDec: IsDecreasing (k :: ls)) ->
  IsSize n (lemma5 proofKLsIsDec) -> IsSize n (lemma5 (succDec proofKLsIsDec))
lemma6 (DecSingle k _) lemma1 = lemma1
lemma6 (DecMany k x xs _ proofXXsIsDec) (MkIsSize (MkPar (x :: xs) proofXXsIsDec)) = MkIsSize (MkPar (x :: xs) proofXXsIsDec)

parNUpperKIsParNUpperSuccK : ParNUpper k n -> ParNUpper (S k) n
parNUpperKIsParNUpperSuccK (MkParNUpper k ls proofKLsIsDec proofLsIsSizeN) =
  MkParNUpper (S k) ls (succDec proofKLsIsDec) (lemma6 proofKLsIsDec proofLsIsSizeN)

parNUpperCons : (k1: Nat) -> (S k1) >= k2 -> ParNUpper k2 n -> ParNUpper (S k1) ((S k1) + n)
parNUpperCons {n=Z} k1 proofSuccK1GteK2 (MkParNUpper k2 Nil (DecSingle _ proofK2IsPos) proofLsIsSizeN) =
  rewrite (plusZeroRightNeutral k1) in
    MkParNUpper (S k1) [S k1] (DecMany (S k1) (S k1) Nil lteRefl (DecSingle (S k1) (LTESucc LTEZero))) (lemma2 k1)
parNUpperCons {n=S x} k1 proofSuccK1GteK2 (MkParNUpper k2 [S x] (DecMany k2 (S x) Nil proofK2GteSuccX proofSuccXNilIsDec) proofXNilIsSizeN) =
  MkParNUpper (S k1) ((S k1) :: (S x) :: Nil)
    (DecMany (S k1) (S k1) [S x] lteRefl (DecMany (S k1) (S x) Nil (lteTransitive proofK2GteSuccX proofSuccK1GteK2) (DecSingle (S x) (LTESucc LTEZero))))
    (lemma3 (S k1) x (lteTransitive proofK2GteSuccX proofSuccK1GteK2))
parNUpperCons k1 proofSuccK1GteK2 (MkParNUpper k2 (x :: y :: ys) (DecMany k2 x (y :: ys) proofK2GteSuccX (DecMany x y ys proofXGteY proofYYsIsDec)) proofXYYsIsSizeN) =
  MkParNUpper (S k1) ((S k1) :: x :: y :: ys)
    (DecMany (S k1) (S k1) (x :: y :: ys) lteRefl (DecMany (S k1) x (y :: ys) (lteTransitive proofK2GteSuccX proofSuccK1GteK2) (DecMany x y ys proofXGteY proofYYsIsDec)))
    (lemma4 (S k1) x y ys proofXYYsIsSizeN (lteTransitive proofK2GteSuccX proofSuccK1GteK2))

plusMinusZero : (a, b: Nat) -> LTE a b -> a + (b `minus` a) = b
plusMinusZero Z Z LTEZero = Refl
plusMinusZero Z (S b) LTEZero = Refl
plusMinusZero (S a) (S b) (LTESucc p) = eqSucc (a + (b `minus` a)) b (plusMinusZero a b p)

naiveAllParNUpper' : (k: Nat) -> (n: Nat) -> List (ParNUpper k n)
naiveAllParNUpper' Z _ = Nil
naiveAllParNUpper' (S k) Z = (MkParNUpper (S k) Nil (DecSingle (S k) (LTESucc LTEZero)) lemma1) :: Nil
naiveAllParNUpper' (S k) n with (isLTE (S k) n)
  | No _ = parNUpperKIsParNUpperSuccK <$> (naiveAllParNUpper' k n)
  | Yes proofSuccKLteN =
    ((parNUpperCons k lteRefl) <$> naiveAllParNUpper' (S k) (assert_smaller n (n `minus` (S k)))) ++ (parNUpperKIsParNUpperSuccK <$> (naiveAllParNUpper' k n))

naiveAllParN' : (n: Nat) -> List (ParN n)
naiveAllParN' Z = (MkParN ParNil lemma1) :: Nil
naiveAllParN' n = forgetUpper' <$> naiveAllParNUpper' n n
