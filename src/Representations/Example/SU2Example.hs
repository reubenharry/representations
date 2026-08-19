{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE KindSignatures #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# LANGUAGE PolyKinds #-}

-- | SU(2) examples for the group-indexed forgetful category ('Representations.Mor').
--
-- @fmap' Fuse@ uses Clebsch–Gordan ('Representations.CG.SU2').
-- @exampleFMoveCommuteHolds@ checks @FMove ∘ fuseLeft = fuseRight ∘ AssocInv@.
module Representations.Example.SU2Example where

import Prelude hiding ((.), id)
import Control.Category.Constrained (Category (..))
import Control.Arrow.Constrained (arr)
import Data.Complex (magnitude)
import Data.Proxy (Proxy (..))
import qualified Data.Vector.Storable as VS
import Math.LinearMap.Category (type (⊗), type (+>), (⊗))
import Math.LinearMap.Asserted (getLinearFunction, type (-+>))
import Math.VectorSpace.DimensionAware (toArray)
import Numeric.LinearAlgebra.Static (C, Sized (..))
import qualified Test.QuickCheck as QC
import Representations.Intertwiner.Random (genIntertwiner)
import Representations.Intertwiner
  ( Intertwiner (..), IntertwinerSectors (..), mkIdHom )
import Representations.Group (Group (SU2))
import Representations.Intertwiner.Pretty (ppr)
import Representations.Mor
import Representations.Rep.Obj (RepObj (..), ToSectors, type Of)
import Representations.Rep.Tensor (Tensor)

-- | Singlet ⊕ triplet (the CG image of ½ ⊗ ½).
type SingletTriplet = '[ 2 `Of` 0, 3 `Of` 2]

type SpinHalf = '[ 1 `Of` 1]

-- | @ToSectors@ keeps the biproduct of multiplicity ⊗ irrep (not a flat @C n@).
_checkToSectors
  :: ToSectors SU2 ('REP '[ 2 `Of` 1, 1 `Of` 2, 1 `Of` 3])
  -> (C 2 ⊗ C 2, (C 1 ⊗ C 3, C 1 ⊗ C 4))
_checkToSectors x = x




type ThreeHalfLeft =
  Tensor SU2 (Tensor SU2 SpinHalf SpinHalf) SpinHalf




type ThreeHalfRight =
  Tensor SU2 SpinHalf (Tensor SU2 SpinHalf SpinHalf)

-- type '[ 1 `Of` 1] = '[ 1 `Of` 1]
-- type ('REP '[ 1 `Of` 1]) = ('REP '[ 1 `Of` 1] :: RepObj SU2)

exampleId :: 'REP '[ 1 `Of` 1] -&> 'REP '[ 1 `Of` 1]
exampleId = RepInter (mkIdHom @SU2)

exampleIdMap :: C 2 -+> C 2
exampleIdMap = fmap' exampleId

exampleIdSectors :: (C 1 ⊗ C 2) -+> (C 1 ⊗ C 2)
exampleIdSectors = fmapSectors exampleId

-- >>> :kind! ThreeHalfLeft
-- ThreeHalfLeft :: [(Natural, Natural)]
-- = '[ '(1, 2), '(3, 1)]

-- | Two spin-½ fuse to singlet ⊕ triplet (CG).
exampleFuse :: ('REP '[ 1 `Of` 1] ':⊗: 'REP '[ 1 `Of` 1]) -&> 'REP '[ 1 `Of` 0, 1 `Of` 2]
exampleFuse = Fuse

exampleFuseThenId :: ('REP '[ 1 `Of` 1] ':⊗: 'REP '[ 1 `Of` 1]) -&> 'REP '[ 1 `Of` 0, 1 `Of` 2]
exampleFuseThenId = RepInter (mkIdHom @SU2 @'[ 1 `Of` 0, 1 `Of` 2]) . Fuse

exampleFuseMap :: (C 2 ⊗ C 2) -+> C 4
exampleFuseMap = fmap' exampleFuse

exampleFuseLM :: (C 2 ⊗ C 2) +> C 4
exampleFuseLM = arr exampleFuseMap

-- | Associator on three spin-½ factors.
exampleAssoc :: ('REP '[ 1 `Of` 1] ':⊗: ('REP '[ 1 `Of` 1] ':⊗: 'REP '[ 1 `Of` 1])) -&> (('REP '[ 1 `Of` 1] ':⊗: 'REP '[ 1 `Of` 1]) ':⊗: 'REP '[ 1 `Of` 1])
exampleAssoc = Assoc

exampleAssocMap :: (C 2 ⊗ (C 2 ⊗ C 2)) -+> ((C 2 ⊗ C 2) ⊗ C 2)
exampleAssocMap = fmap' exampleAssoc

exampleAssocInv :: ((('REP '[ 1 `Of` 1]) ':⊗: ('REP '[ 1 `Of` 1])) ':⊗: ('REP '[ 1 `Of` 1])) -&> (('REP '[ 1 `Of` 1]) ':⊗: (('REP '[ 1 `Of` 1]) ':⊗: ('REP '[ 1 `Of` 1])))
exampleAssocInv = AssocInv

-- | Swap two spin-½ factors.
exampleSwap :: ('REP '[ 1 `Of` 1] ':⊗: 'REP '[ 1 `Of` 2]) -&> ('REP '[ 1 `Of` 2] ':⊗: 'REP '[ 1 `Of` 1])
exampleSwap = Swap

exampleSwapMap :: (C 2 ⊗ C 3) -+> (C 3 ⊗ C 2)
exampleSwapMap = fmap' exampleSwap

-- | Right unitor on spin-½.
exampleRUnit :: ('REP '[ 1 `Of` 1] ':⊗: 'I) -&> 'REP '[ 1 `Of` 1]
exampleRUnit = RUnit

exampleRUnitMap :: (C 2 ⊗ C 1) -+> C 2
exampleRUnitMap = fmap' exampleRUnit


-- | Monoidal product of two identity morphisms (stays symbolic until fmap').
exampleOTimes :: ('REP '[ 1 `Of` 1] ':⊗: 'REP '[ 1 `Of` 1]) -&> ('REP '[ 1 `Of` 1] ':⊗: 'REP '[ 1 `Of` 1])
exampleOTimes = OTimes exampleId exampleId

exampleOTimesMap :: (C 2 ⊗ C 2) -+> (C 2 ⊗ C 2)
exampleOTimesMap = fmap' exampleOTimes

-- | F-move on three spin-½ fusions: @(½⊗½)⊗½ → ½⊗(½⊗½)@.
-- Carries Schur F-symbols; @fmap'@ densifies via @intertwinerLinear@.
exampleFMove
  :: 'REP ['(1, 2), '(3, 1)] -&> 'REP ['(1, 2), '(3, 1)]
exampleFMove = fMoveSU2 (Proxy @SpinHalf) (Proxy @SpinHalf) (Proxy @SpinHalf)

exampleFMoveInv
  :: 'REP ['(1, 2), '(3, 1)] -&> 'REP ['(1, 2), '(3, 1)]
exampleFMoveInv = fMoveSU2Inv (Proxy @SpinHalf) (Proxy @SpinHalf) (Proxy @SpinHalf)

exampleFMoveMap
  :: C 8 -+> C 8
exampleFMoveMap = fmap' exampleFMove

exampleFMoveSectors
  :: (C 2 ⊗ C 2, C 1 ⊗ C 4) -+> (C 2 ⊗ C 2, C 1 ⊗ C 4)
exampleFMoveSectors = fmapSectors exampleFMove

-- | Left fusion tree: fuse the first pair, then the remaining factor.
-- @(½ ⊗ ½) ⊗ ½ → Tensor (Tensor ½ ½) ½@.
exampleFuseLeft
  :: ((('REP SpinHalf) ':⊗: ('REP SpinHalf)) ':⊗: ('REP SpinHalf))
     -&> 'REP ThreeHalfLeft
exampleFuseLeft = Fuse . OTimes Fuse exampleId

-- | Right fusion tree: fuse the second pair, then the remaining factor.
-- @½ ⊗ (½ ⊗ ½) → Tensor ½ (Tensor ½ ½)@.
exampleFuseRight
  :: (('REP SpinHalf) ':⊗: (('REP SpinHalf) ':⊗: ('REP SpinHalf)))
     -&> 'REP ThreeHalfRight
exampleFuseRight = Fuse . OTimes exampleId exampleFuse

exampleFMoveViaFuseMap :: ((C 2 ⊗ C 2) ⊗ C 2) -+> C 8
exampleFMoveViaFuseMap = fmap' (fMoveSU2 (Proxy @SpinHalf) (Proxy @SpinHalf) (Proxy @SpinHalf) . exampleFuseLeft)

exampleFMoveViaReassocMap :: ((C 2 ⊗ C 2) ⊗ C 2) -+> C 8
exampleFMoveViaReassocMap = fmap' (exampleFuseRight . exampleAssocInv)

spinHalfBasis :: [C 2]
spinHalfBasis =
  [ fromList [1, 0]
  , fromList [0, 1]
  ]

tripleProductBasis :: [(C 2 ⊗ C 2) ⊗ C 2]
tripleProductBasis =
  [ (x ⊗ y) ⊗ z
  | x <- spinHalfBasis
  , y <- spinHalfBasis
  , z <- spinHalfBasis
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
exampleRMove
  :: 'REP ['(0, 1), '(2, 1)] -&> 'REP ['(0, 1), '(2, 1)]
exampleRMove = rMoveSU2 (Proxy @'[ 1 `Of` 1]) (Proxy @'[ 1 `Of` 1])

exampleRMoveMap :: C 4 -+> C 4
exampleRMoveMap = fmap' exampleRMove

exampleRMoveSectors
  :: (C 1 ⊗ C 1, C 1 ⊗ C 3) -+> (C 1 ⊗ C 1, C 1 ⊗ C 3)
exampleRMoveSectors = fmapSectors exampleRMove

example :: 'REP '[ 1 `Of` 1] -&> 'REP '[ 1 `Of` 2]
example = RepInter (MkIntertwiner InterNil)

example' :: C 2 +> C 3
example' = arr (fmap' example)

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
