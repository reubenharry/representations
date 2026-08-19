{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PolyKinds #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Sampling of Schur-block intertwiners.
module Representations.Intertwiner.Random
  ( genGaussian
  , genComplexGaussian
  , genMat
  , genCoeffBlock
  , GenHomSectors (..)
  , genIntertwiner
  ) where

import Control.Monad (replicateM)
import Data.Complex (Complex (..))
import Data.Proxy (Proxy (..))
import GHC.TypeLits (KnownNat, Nat, natVal, type (*))
import Numeric.LinearAlgebra.Static (M, Sized (fromList))
import qualified Test.QuickCheck as QC
import Representations.Intertwiner
  ( Intertwiner (..), IntertwinerSectors (..) )
import Representations.Group (Group (..), Irreps, IntertwinerHom)
import Representations.Rep.HomBlock (HomBlockDim, CoeffBlock (..))

--------------------------------------------------------------------------------
-- Scalars
--------------------------------------------------------------------------------

-- | Standard normal via Box–Muller (QuickCheck 'Gen').
genGaussian :: QC.Gen Double
genGaussian = do
  u1 <- QC.choose (1e-12, 1 - 1e-12)
  u2 <- QC.choose (0, 1)
  let r = sqrt (-2 * log u1)
      theta = 2 * pi * u2
  pure (r * cos theta)

-- | Complex normal with i.i.d. @N(0,1)@ real\/imag parts.
genComplexGaussian :: QC.Gen (Complex Double)
genComplexGaussian = (:+) <$> genGaussian <*> genGaussian

--------------------------------------------------------------------------------
-- Dense maps / Schur blocks
--------------------------------------------------------------------------------

genMat :: forall m n. (KnownNat m, KnownNat n, KnownNat (m * n)) => QC.Gen (M m n)
genMat = do
  let entries = fromIntegral (natVal (Proxy @(m * n)))
  xs <- replicateM entries genComplexGaussian
  pure (fromList xs)

genCoeffBlock
  :: forall m n. (KnownNat m, KnownNat n, KnownNat (HomBlockDim m n))
  => QC.Gen (CoeffBlock m n)
genCoeffBlock = CoeffBlock <$> genMat @m @n

-- | Draw one independent coefficient block per hom-sector entry.
class GenHomSectors (g :: Group) (hom :: [(Irreps g, Nat, Nat)]) where
  genHomSectors :: QC.Gen (IntertwinerSectors g hom)

instance GenHomSectors U1 '[] where
  genHomSectors = pure InterNil

instance
  ( KnownNat m, KnownNat n, KnownNat (HomBlockDim m n)
  , GenHomSectors U1 rest
  ) => GenHomSectors U1 ('(j, m, n) ': rest) where
  genHomSectors = InterCons <$> genCoeffBlock @m @n <*> genHomSectors

instance GenHomSectors SU2 '[] where
  genHomSectors = pure InterNil

instance
  ( KnownNat m, KnownNat n, KnownNat (HomBlockDim m n)
  , GenHomSectors SU2 rest
  ) => GenHomSectors SU2 ('(j, m, n) ': rest) where
  genHomSectors = InterCons <$> genCoeffBlock @m @n <*> genHomSectors

genIntertwiner
  :: forall g r q
   . GenHomSectors g (IntertwinerHom g r q)
  => QC.Gen (Intertwiner g r q)
genIntertwiner = MkIntertwiner <$> genHomSectors
