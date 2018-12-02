module Partition

import Data.PosNat
import Data.So

%default total

-- define equality of PosNat

Eq PosNat where
  (x ** _) == (y ** _) = x == y

-- prove X >= Y

IsPosGte : PosNat -> PosNat -> Type
IsPosGte (x ** _) (y ** _) = So (x >= y)

mkIsPosGte : (x: PosNat) -> (y: PosNat) -> Maybe (IsPosGte x y)
mkIsPosGte (xn ** _) (yn ** _) =
  case (choose (xn >= yn)) of
    Left  proofXGteY => Just proofXGteY
    Right proofNotXGteY => Nothing

-- prove X is sorted 

data IsPosSorted : List PosNat -> Type where
  IsPosSortedZero :
    IsPosSorted Nil

  IsPosSortedOne :
    (x: PosNat) -> IsPosSorted (x :: Nil)

  IsPosSortedMany :
    (x: PosNat) -> (y: PosNat) -> (ys: List PosNat) ->
    (IsPosGte x y) -> (IsPosSorted (y :: ys)) ->
    IsPosSorted (x :: (y :: ys))

mkIsPosSorted : (xs: List PosNat) -> Maybe (IsPosSorted xs)
mkIsPosSorted Nil =
  Just IsPosSortedZero
mkIsPosSorted (x :: Nil) =
  Just (IsPosSortedOne x)
mkIsPosSorted (x :: (y :: ys)) =
  case (mkIsPosGte x y) of
    Just proofXGteY =>
      case (mkIsPosSorted (y :: ys)) of
        Just proofYYsIsSorted =>
          Just (IsPosSortedMany x y ys proofXGteY proofYYsIsSorted)

        Nothing =>
          Nothing

    Nothing =>
      Nothing

-- define partiton set Par

export
Par : Type
Par = DPair (List PosNat) IsPosSorted

export
mkPar : List PosNat -> Maybe Par
mkPar xs =
  case (mkIsPosSorted xs) of
    Just proofXsIsSorted =>
      Just (MkDPair xs proofXsIsSorted)

    Nothing =>
      Nothing

-- define utility functions about Par

export
length : Par -> Nat
length l = length $ fst l

export
index : Nat -> Par -> Maybe PosNat
index n l = index' n (fst l)

export
multiplicity : PosNat -> Par -> Nat
multiplicity e l = length $ elemIndices e (fst l)

export
size : Par -> Nat
size l = foldl (\a, b => a + (fst b)) Z (fst l)

-- define partition set every size of whose element is just N

IsSize : Nat -> Par -> Type
IsSize n l = So (size l == n)

export
ParN : Nat -> Type
ParN n = DPair Par (IsSize n)

export
mkParN : (n: Nat) -> (l: Par) -> Maybe (ParN n)
mkParN n l =
  case (choose (size l == n)) of
    Left proofLIsSizeN =>
      Just (MkDPair l proofLIsSizeN)

    Right proofLIsNotSizeN =>
      Nothing

