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
  do
    proofXGteY <- mkIsPosGte x y
    proofYYsIsSorted <- mkIsPosSorted (y :: ys)
    Just (IsPosSortedMany x y ys proofXGteY proofYYsIsSorted)

-- define partiton set Par

export
Par : Type
Par = DPair (List PosNat) IsPosSorted

export
mkPar : List PosNat -> Maybe Par
mkPar xs =
  do
    proofXsIsSorted <- mkIsPosSorted xs
    Just (MkDPair xs proofXsIsSorted)

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

