{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Hom blocks between matching-irrep sector copies.
--
-- By Schur, @Hom(V_j^{⊕n}, V_j^{⊕m}) ≅ M_{m,n}(C)@ for every compact group:
-- @m × n@ scalar coefficients, each acting as @λ · I@ on the irrep factor.
-- U(1) embeds those coefficients directly as @M m n@; SU(2) expands via
-- @kron(coeffMat, I_{j+1})@.
module Representations.Rep.HomBlock where

import Data.Complex (Complex)
import Data.Maybe (fromMaybe)
import GHC.TypeLits (Nat, KnownNat, natVal, type (*))
import Data.Proxy (Proxy (..))
import Numeric.LinearAlgebra.Static
  (C, M, konst, extract, Sized(fromList, unwrap, create), Domain(app, mul))
import qualified Numeric.LinearAlgebra as LA
import Numeric.LinearAlgebra.Static.COrphans ()  -- Eq (C n)
import Representations.Group (Group (..), IrrepDim, SectorDim, Irreps)

-- | Parameter count for a flat @CoeffBlock@ (multiplicity coefficient layer).
type family HomBlockDim (m :: Nat) (n :: Nat) :: Nat where
  HomBlockDim m n = m * n

-- | Multiplicity coefficient matrix shared by all groups' Hom blocks
-- (Schur: @Hom(V_j^{⊕n}, V_j^{⊕m}) ≅ M_{m,n}(C)@).
newtype CoeffBlock (m :: Nat) (n :: Nat) = CoeffBlock
  { unCoeffBlock :: M m n }

instance (KnownNat m, KnownNat n, KnownNat (m * n)) => Show (CoeffBlock m n) where
  show (CoeffBlock v) = show v

instance (KnownNat m, KnownNat n) => Eq (CoeffBlock m n) where
  CoeffBlock a == CoeffBlock b =
    LA.flatten (unwrap a) == LA.flatten (unwrap b)

coeffBlockAsMat
  :: forall m n d. (KnownNat m, KnownNat n, KnownNat d, HomBlockDim m n ~ d)
  => CoeffBlock m n -> M m n
coeffBlockAsMat (CoeffBlock block) = block --  fromList (toList (extract block))

composeCoeffBlock
  :: forall m n p d1 d2 d3.
     ( KnownNat m, KnownNat n, KnownNat p
     , KnownNat d1, KnownNat d2, KnownNat d3
     , HomBlockDim m n ~ d1, HomBlockDim n p ~ d2, HomBlockDim m p ~ d3 )
  => CoeffBlock m n -> CoeffBlock n p -> CoeffBlock m p
composeCoeffBlock ab bc = CoeffBlock (prod)
  where
    prod = mul (coeffBlockAsMat ab) (coeffBlockAsMat bc)

zeroCoeffBlock
  :: forall m n. (KnownNat m, KnownNat n, KnownNat (HomBlockDim m n))
  => CoeffBlock m n
zeroCoeffBlock = CoeffBlock (konst 0)

addCoeffBlock
  :: forall m n. (KnownNat m, KnownNat n)
  => CoeffBlock m n -> CoeffBlock m n -> CoeffBlock m n
addCoeffBlock (CoeffBlock a) (CoeffBlock b) = CoeffBlock (a + b)

scaleCoeffBlock
  :: forall m n. (KnownNat m, KnownNat n)
  => Complex Double -> CoeffBlock m n -> CoeffBlock m n
scaleCoeffBlock μ (CoeffBlock m) =
  CoeffBlock
    (fromMaybe (error "scaleCoeffBlock: create failed") . create $
       LA.cmap (* μ) (extract m))

negateCoeffBlock
  :: forall m n. (KnownNat m, KnownNat n)
  => CoeffBlock m n -> CoeffBlock m n
negateCoeffBlock (CoeffBlock m) =
  CoeffBlock
    (fromMaybe (error "negateCoeffBlock: create failed") . create $
       LA.cmap negate (extract m))

applyBlock
  :: forall m n d. (KnownNat m, KnownNat n, KnownNat d, HomBlockDim m n ~ d)
  => CoeffBlock m n -> C n -> C m
applyBlock blk = app (coeffBlockAsMat blk)

eyeBlock
  :: forall m. (KnownNat m, KnownNat (HomBlockDim m m))
  => CoeffBlock m m
eyeBlock =
  let n = fromIntegral (natVal (Proxy @m)) :: Int
   in CoeffBlock $
        fromList
          [ if i == j then 1 else 0
          | i <- [0 .. n - 1]
          , j <- [0 .. n - 1]
          ]

su2ExpandBlock
  :: forall spin m n.
     (KnownNat m, KnownNat n, KnownNat (IrrepDim SU2 spin))
  => CoeffBlock m n -> M (SectorDim SU2 spin m) (SectorDim SU2 spin n)
su2ExpandBlock blk =
  fromList $
    LA.toList $
      LA.flatten $
        LA.kronecker
          (unwrap (coeffBlockAsMat blk))
          (LA.ident (fromIntegral (natVal (Proxy @(IrrepDim SU2 spin)))))

-- | Expand a Schur coefficient block to the sector map
-- (@M_{m,n}@ for U(1); @kron(coeff, I_{j+1})@ for SU(2)).
class ExpandBlock (g :: Group) where
  expandBlock
    :: forall (j :: Irreps g) m n.
       ( KnownNat m, KnownNat n
       , KnownNat (SectorDim g j m)
       , KnownNat (SectorDim g j n)
       , KnownNat (IrrepDim g j)
       )
    => Proxy j
    -> CoeffBlock m n
    -> M (SectorDim g j m) (SectorDim g j n)

instance ExpandBlock U1 where
  expandBlock _ = coeffBlockAsMat

instance ExpandBlock SU2 where
  expandBlock (_ :: Proxy j) = su2ExpandBlock @j
