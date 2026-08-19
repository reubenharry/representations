{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Hom blocks between matching-irrep sector copies.
--
-- By Schur, @Hom(V_j^{⊕n}, V_j^{⊕m}) ≅ M_{m,n}(C)@ for every compact group:
-- @m × n@ scalar coefficients, each acting as @λ · I@ on the irrep factor.
-- U(1) embeds those coefficients directly as @M m n@; SU(2) expands via
-- @kron(coeffMat, I_{j+1})@.
module Representations.Rep.HomBlock
  ( HomBlockDim,
    composeBlock,
    zeroBlock,
    addBlock,
    scaleBlock,
    negateBlock,
    applyBlock,
    eyeBlock,
    ExpandBlock (..),
  )
where

import Data.Complex (Complex)
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (..))
import GHC.TypeLits (KnownNat, Nat, natVal, type (*))
import qualified Numeric.LinearAlgebra as LA
import Numeric.LinearAlgebra.Static
  ( C,
    Domain (app, mul),
    M,
    Sized (create, fromList, unwrap),
    extract,
    konst,
  )
import Numeric.LinearAlgebra.Static.COrphans ()
import Representations.Group (Group (..), IrrepDim, Irreps, SectorDim)

-- | Parameter count for a flat Schur coefficient matrix.
type family HomBlockDim (m :: Nat) (n :: Nat) :: Nat where
  HomBlockDim m n = m * n

instance (KnownNat m, KnownNat n) => Eq (M m n) where
  a == b = LA.flatten (unwrap a) == LA.flatten (unwrap b)

composeBlock ::
  forall m n p.
  (KnownNat m, KnownNat n, KnownNat p) =>
  M m n ->
  M n p ->
  M m p
composeBlock = mul

zeroBlock ::
  forall m n.
  (KnownNat m, KnownNat n, KnownNat (HomBlockDim m n)) =>
  M m n
zeroBlock = konst 0

addBlock ::
  forall m n.
  (KnownNat m, KnownNat n) =>
  M m n ->
  M m n ->
  M m n
addBlock = (+)

scaleBlock ::
  forall m n.
  (KnownNat m, KnownNat n) =>
  Complex Double ->
  M m n ->
  M m n
scaleBlock μ m =
  fromMaybe (error "scaleBlock: create failed") . create $
    LA.cmap (* μ) (extract m)

negateBlock ::
  forall m n.
  (KnownNat m, KnownNat n) =>
  M m n ->
  M m n
negateBlock m =
  fromMaybe (error "negateBlock: create failed") . create $
    LA.cmap negate (extract m)

applyBlock ::
  forall m n.
  (KnownNat m, KnownNat n) =>
  M m n ->
  C n ->
  C m
applyBlock = app

eyeBlock ::
  forall m.
  (KnownNat m, KnownNat (HomBlockDim m m)) =>
  M m m
eyeBlock =
  let n = fromIntegral (natVal (Proxy @m)) :: Int
   in fromList
        [ if i == j then 1 else 0
        | i <- [0 .. n - 1],
          j <- [0 .. n - 1]
        ]

su2ExpandBlock ::
  forall spin m n.
  (KnownNat m, KnownNat n, KnownNat (IrrepDim SU2 spin)) =>
  M m n ->
  M (SectorDim SU2 spin m) (SectorDim SU2 spin n)
su2ExpandBlock blk =
  fromList $
    LA.toList $
      LA.flatten $
        LA.kronecker
          (unwrap blk)
          (LA.ident (fromIntegral (natVal (Proxy @(IrrepDim SU2 spin)))))

-- | Expand a Schur coefficient block to the sector map
-- (@M_{m,n}@ for U(1); @kron(coeff, I_{j+1})@ for SU(2)).
class ExpandBlock (g :: Group) where
  expandBlock ::
    forall (j :: Irreps g) m n.
    ( KnownNat m,
      KnownNat n,
      KnownNat (SectorDim g j m),
      KnownNat (SectorDim g j n),
      KnownNat (IrrepDim g j)
    ) =>
    Proxy j ->
    M m n ->
    M (SectorDim g j m) (SectorDim g j n)

instance ExpandBlock U1 where
  expandBlock _ = id

instance ExpandBlock SU2 where
  expandBlock (_ :: Proxy j) = su2ExpandBlock @j
