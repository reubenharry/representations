{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | SU(2) examples for the group-indexed forgetful category ('Representations.Mor').
--
-- @fmap' Fuse@ uses Clebsch–Gordan ('Representations.CG.SU2').
-- @exampleFMoveCommuteHolds@ checks @FMove ∘ fuseLeft = fuseRight ∘ AssocInv@.
module Representations.Example.SU2Example where

import Control.Arrow.Constrained (arr)
import Control.Category.Constrained (Category (..))
import Data.Complex (magnitude)
import Data.Proxy (Proxy (..))
import qualified Data.Vector.Storable as VS
import Data.VectorSpace (AdditiveGroup ((^+^)))
import Math.LinearMap.Asserted (getLinearFunction, type (-+>))
import Math.LinearMap.Category ((⊗), type (+>), type (⊗))
import Math.VectorSpace.DimensionAware (toArray)
import Numeric.LinearAlgebra.Static (C, Sized (..), M)
import Representations.Group (Group (SU2), IntertwinerHom)
import Representations.Intertwiner
  ( HasIntertwiner,
    Intertwiner (..),
    IntertwinerSectors (..),
    mkIdHom,
  )
import Representations.Intertwiner.Pretty (ppr)
import Representations.Intertwiner.Random (genIntertwiner)
import Representations.Mor
import Representations.Rep.Obj (RepObj (..), ToSectors, type Of, type (⊕))
import Representations.Rep.Tensor (Tensor)
import Representations.Utils (mat, vec)
import qualified Test.QuickCheck as QC
import Prelude hiding (id, (.))
import GHC.TypeLits (KnownNat)
import Representations.Rep.HomBlock (HomBlockDim)

example1 :: C 2
example1 = vec (1, 2)

example2 :: C 3
example2 = vec (5, 6, 4)

exampleTensorSum :: C 3 ⊗ C 2
exampleTensorSum =
  vec (5, 6, 4) ⊗ vec (1, 2)

-- | Singlet ⊕ triplet (the CG image of ½ ⊗ ½).
type SingletTriplet = (2 `Of` 0) ⊕ (3 `Of` 2)

type OneSpinHalf = '[1 `Of` 1]

-- | @ToSectors@ keeps the biproduct of multiplicity ⊗ irrep (not a flat @C n@).
_checkToSectors ::
  ToSectors SU2 ('REP '[2 `Of` 1, 1 `Of` 2, 1 `Of` 3]) ->
  (C 2 ⊗ C 2, (C 1 ⊗ C 3, C 1 ⊗ C 4))
_checkToSectors x = x

type ThreeHalfLeft =
  Tensor SU2 (Tensor SU2 OneSpinHalf OneSpinHalf) OneSpinHalf

type ThreeHalfRight =
  Tensor SU2 OneSpinHalf (Tensor SU2 OneSpinHalf OneSpinHalf)

-- type '[ 1 `Of` 1] = '[ 1 `Of` 1]
-- type ('REP '[ 1 `Of` 1]) = ('REP '[ 1 `Of` 1] :: RepObj SU2)

exampleId :: 'REP '[1 `Of` 1] -&> 'REP '[1 `Of` 1]
exampleId = RepInter (mkIdHom @SU2)

exampleIdMap :: C 2 -+> C 2
exampleIdMap = fmap' exampleId

exampleIdSectors :: (C 1 ⊗ C 2) -+> (C 1 ⊗ C 2)
exampleIdSectors = fmapSectors exampleId

-- >>> :kind! ThreeHalfLeft
-- ThreeHalfLeft :: [(Natural, Natural)]
-- = '[ '(1, 2), '(3, 1)]

-- | Two spin-½ fuse to singlet ⊕ triplet (CG).
exampleFuse :: ('REP '[1 `Of` 1] ':⊗: 'REP '[1 `Of` 1]) -&> 'REP '[1 `Of` 0, 1 `Of` 2]
exampleFuse = Fuse

exampleFuseThenId :: ('REP '[1 `Of` 1] ':⊗: 'REP '[1 `Of` 1]) -&> 'REP '[1 `Of` 0, 1 `Of` 2]
exampleFuseThenId = RepInter (mkIdHom @SU2 @'[1 `Of` 0, 1 `Of` 2]) . Fuse

exampleFuseMap :: (C 2 ⊗ C 2) -+> C 4
exampleFuseMap = fmap' exampleFuse

exampleFuseLM :: (C 2 ⊗ C 2) +> C 4
exampleFuseLM = arr exampleFuseMap

-- | Associator on three spin-½ factors.
exampleAssoc :: ('REP '[1 `Of` 1] ':⊗: ('REP '[1 `Of` 1] ':⊗: 'REP '[1 `Of` 1])) -&> (('REP '[1 `Of` 1] ':⊗: 'REP '[1 `Of` 1]) ':⊗: 'REP '[1 `Of` 1])
exampleAssoc = Assoc

exampleAssocMap :: (C 2 ⊗ (C 2 ⊗ C 2)) -+> ((C 2 ⊗ C 2) ⊗ C 2)
exampleAssocMap = fmap' exampleAssoc

exampleAssocInv :: ((('REP '[1 `Of` 1]) ':⊗: ('REP '[1 `Of` 1])) ':⊗: ('REP '[1 `Of` 1])) -&> (('REP '[1 `Of` 1]) ':⊗: (('REP '[1 `Of` 1]) ':⊗: ('REP '[1 `Of` 1])))
exampleAssocInv = AssocInv

-- | Swap two spin-½ factors.
exampleSwap :: ('REP '[1 `Of` 1] ':⊗: 'REP '[1 `Of` 2]) -&> ('REP '[1 `Of` 2] ':⊗: 'REP '[1 `Of` 1])
exampleSwap = Swap

exampleSwapMap :: (C 2 ⊗ C 3) -+> (C 3 ⊗ C 2)
exampleSwapMap = fmap' exampleSwap

-- | Right unitor on spin-½.
exampleRUnit :: ('REP '[1 `Of` 1] ':⊗: 'I) -&> 'REP '[1 `Of` 1]
exampleRUnit = RUnit

exampleRUnitMap :: (C 2 ⊗ C 1) -+> C 2
exampleRUnitMap = fmap' exampleRUnit

-- | Monoidal product of two identity morphisms (stays symbolic until fmap').
exampleOTimes :: ('REP '[1 `Of` 1] ':⊗: 'REP '[1 `Of` 1]) -&> ('REP '[1 `Of` 1] ':⊗: 'REP '[1 `Of` 1])
exampleOTimes = OTimes exampleId exampleId

exampleOTimesMap :: (C 2 ⊗ C 2) -+> (C 2 ⊗ C 2)
exampleOTimesMap = fmap' exampleOTimes

-- | F-move on three spin-½ fusions: @(½⊗½)⊗½ → ½⊗(½⊗½)@.
-- Carries Schur F-symbols; @fmap'@ densifies via @intertwinerLinear@.
exampleFMove ::
  'REP ['(1, 2), '(3, 1)] -&> 'REP ['(1, 2), '(3, 1)]
exampleFMove = fMoveSU2 (Proxy @OneSpinHalf) (Proxy @OneSpinHalf) (Proxy @OneSpinHalf)

exampleFMoveInv ::
  'REP ['(1, 2), '(3, 1)] -&> 'REP ['(1, 2), '(3, 1)]
exampleFMoveInv = fMoveSU2Inv (Proxy @OneSpinHalf) (Proxy @OneSpinHalf) (Proxy @OneSpinHalf)

exampleFMoveMap ::
  C 8 -+> C 8
exampleFMoveMap = fmap' exampleFMove

exampleFMoveSectors ::
  (C 2 ⊗ C 2, C 1 ⊗ C 4) -+> (C 2 ⊗ C 2, C 1 ⊗ C 4)
exampleFMoveSectors = fmapSectors exampleFMove

-- | Left fusion tree: fuse the first pair, then the remaining factor.
-- @(½ ⊗ ½) ⊗ ½ → Tensor (Tensor ½ ½) ½@.
exampleFuseLeft ::
  ((('REP OneSpinHalf) ':⊗: ('REP OneSpinHalf)) ':⊗: ('REP OneSpinHalf))
    -&> 'REP ThreeHalfLeft
exampleFuseLeft = Fuse . OTimes Fuse exampleId

-- | Right fusion tree: fuse the second pair, then the remaining factor.
-- @½ ⊗ (½ ⊗ ½) → Tensor ½ (Tensor ½ ½)@.
exampleFuseRight ::
  (('REP OneSpinHalf) ':⊗: (('REP OneSpinHalf) ':⊗: ('REP OneSpinHalf)))
    -&> 'REP ThreeHalfRight
exampleFuseRight = Fuse . OTimes exampleId exampleFuse

exampleFMoveViaFuseMap :: ((C 2 ⊗ C 2) ⊗ C 2) -+> C 8
exampleFMoveViaFuseMap = fmap' (fMoveSU2 (Proxy @OneSpinHalf) (Proxy @OneSpinHalf) (Proxy @OneSpinHalf) . exampleFuseLeft)

exampleFMoveViaReassocMap :: ((C 2 ⊗ C 2) ⊗ C 2) -+> C 8
exampleFMoveViaReassocMap = fmap' (exampleFuseRight . exampleAssocInv)

spinHalfBasis :: [C 2]
spinHalfBasis =
  [ fromList [1, 0],
    fromList [0, 1]
  ]

tripleProductBasis :: [(C 2 ⊗ C 2) ⊗ C 2]
tripleProductBasis =
  [ (x ⊗ y) ⊗ z
  | x <- spinHalfBasis,
    y <- spinHalfBasis,
    z <- spinHalfBasis
  ]

-- | @True@ iff the square commutes: @FMove ∘ fuseLeft = fuseRight ∘ α⁻¹@.
exampleFMoveCommuteHolds :: Bool
exampleFMoveCommuteHolds =
  all agree tripleProductBasis
  where
    agree v =
      let a = toArray (getLinearFunction exampleFMoveViaFuseMap v)
          b = toArray (getLinearFunction exampleFMoveViaReassocMap v)
       in VS.and $ VS.zipWith (\x y -> magnitude (x - y) < 1e-10) a b

-- | Print whether the F-move square commutes on three spin-½ factors.
exampleFMoveCommute :: IO ()
exampleFMoveCommute =
  putStrLn $
    if exampleFMoveCommuteHolds
      then "F-move commutes with reassoc: OK"
      else "F-move commutes with reassoc: FAIL"

-- | R-move on fused ½⊗½ (singlet ⊕ triplet): @Tensor ½ ½ → Tensor ½ ½@.
exampleRMove ::
  'REP ['(0, 1), '(2, 1)] -&> 'REP ['(0, 1), '(2, 1)]
exampleRMove = rMoveSU2 (Proxy @'[1 `Of` 1]) (Proxy @'[1 `Of` 1])

exampleRMoveMap :: C 4 -+> C 4
exampleRMoveMap = fmap' exampleRMove

exampleRMoveSectors ::
  (C 1 ⊗ C 1, C 1 ⊗ C 3) -+> (C 1 ⊗ C 1, C 1 ⊗ C 3)
exampleRMoveSectors = fmapSectors exampleRMove

intertwiner ::
  (HasIntertwiner g r q) =>
  IntertwinerSectors g (IntertwinerHom g r q) ->
  Mor g ('REP r) ('REP q)
intertwiner = RepInter . MkIntertwiner

type SpinHalf = 1
type SpinZero = 0
type SpinOne = 2


mkBlock ::
    ( KnownNat m,
      KnownNat n,
      KnownNat (HomBlockDim m n)
    ) =>
    M m n ->
    IntertwinerSectors g rest ->
    IntertwinerSectors g ('(j, m, n) ': rest)

mkBlock = InterCons


-- | Fuse (2×½)⊗½, then retain singlet + triplet sectors at @'[2 `Of` 0, 1 `Of` 2]@.
exampleDupHalfInter :: ('REP '[2 `Of` SpinHalf] :⊗: 'REP '[1 `Of` SpinHalf]) -&> 'REP ((2 `Of` SpinZero) ⊕ (1 `Of` SpinOne))
exampleDupHalfInter = intertwiner (   

  mkBlock (mat (1, 0, 0, 1))
  (mkBlock (mat (1, 1))

  InterNil )) `Comp`Fuse


-- exampleDupHalfMap :: C 2 -+> C 4
-- exampleDupHalfMap = fmap' exampleDupHalf

-- | @vec (1,0)@ mapped to two identical spin-½ copies.
-- exampleDupHalfOnVec :: C 4
-- exampleDupHalfOnVec = getLinearFunction exampleDupHalfMap (vec (1, 0))

-- | Random endomorphism of singlet ⊕ triplet (independent Schur blocks).
genSingletTripletEndo :: QC.Gen (Intertwiner SU2 SingletTriplet SingletTriplet)
genSingletTripletEndo = genIntertwiner @SU2

-- | Draw one sample and print Schur + dense block-diagonal forms.
exampleRandomIntertwiner :: IO ()
exampleRandomIntertwiner = do
  inter <- QC.generate genSingletTripletEndo
  ppr inter
  putStrLn "----"
  ppr inter
