{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Apply a same-spine intertwiner on 'RepToSectors': zip sectors and apply
-- @coeff ⊗ id@ on each multiplicity ⊗ irrep block.
module Representations.Rep.Sectors
  ( ApplyHom (..),
    applySector,
    intertwinerEndoSectors,
    (⊗^),
  )
where

import Control.Arrow.Constrained (arr, ($))
import Control.Category.Constrained (id)
import Data.Complex (Complex)
import Data.VectorSpace (VectorSpace)
import GHC.TypeLits (KnownNat, Nat, type (*))
import Math.LinearMap.Asserted (linearFunction, type (-+>))
import Math.LinearMap.Category
  ( LSpace,
    LinearSpace,
    Scalar,
    TensorSpace,
    tensorOfMaps,
    (-+$>),
    type (+>),
    type (⊗),
  )
import Numeric.LinearAlgebra.Static (C, M)
import Numeric.LinearAlgebra.Static.COrphans ()
import Representations.Group (Group (..), IntertwinerHom, IrrepDim, Irreps, Rep)
import Representations.Intertwiner
  ( Intertwiner (..),
    IntertwinerSectors (..),
  )
import Representations.Rep.HomBlock (HomBlockDim, applyBlock)
import Representations.Rep.Obj (RepToSectors)
import Prelude hiding (id, ($), (.))

type ℂ = Complex Double

-- | linearmap-family dictionaries for @coeff ⊗ id@ on a multiplicity ⊗ irrep sector.
type ApplySectorC m n d =
  ( KnownNat m,
    KnownNat n,
    KnownNat d,
    KnownNat (HomBlockDim m n),
    HomBlockDim m n ~ (m * n),
    LSpace (C n),
    LSpace (C m),
    LSpace (C d),
    LSpace (C n ⊗ C d),
    LSpace (C m ⊗ C d),
    TensorSpace (C n ⊗ C d),
    TensorSpace (C m ⊗ C d),
    LinearSpace (C d),
    Scalar (C n) ~ ℂ,
    Scalar (C m) ~ ℂ,
    Scalar (C d) ~ ℂ
  )

-- | @(f ⊗^ g) $ (x ⊗ y) = (f $ x) ⊗ (g $ y)@
(⊗^) ::
  forall u v u' v'.
  ( LSpace u,
    LSpace u',
    LSpace v,
    LSpace v',
    TensorSpace v,
    TensorSpace v',
    TensorSpace (u ⊗ u'),
    TensorSpace (v ⊗ v'),
    Scalar u ~ Scalar u',
    Scalar u ~ Scalar v,
    Scalar v ~ Scalar v'
  ) =>
  (u +> v) -> (u' +> v') -> ((u ⊗ u') +> (v ⊗ v'))
f ⊗^ g = (tensorOfMaps -+$> f) -+$> g

infixr 7 ⊗^

-- | @coeff ⊗ id@ on a multiplicity ⊗ irrep sector.
applySector ::
  forall m n d.
  (ApplySectorC m n d) =>
  M m n ->
  (C n ⊗ C d) ->
  (C m ⊗ C d)
applySector blk v =
  (arr (linearFunction (applyBlock blk)) ⊗^ (id :: C d +> C d)) $ v

-- | Zip a hom-spine against a matching reduced spine.
class
  ApplyHom
    (g :: Group)
    (hom :: [(Irreps g, Nat, Nat)])
    (r :: Rep g)
  where
  applyHom ::
    IntertwinerSectors g hom ->
    RepToSectors g r ->
    RepToSectors g r

intertwinerEndoSectors ::
  forall g r.
  ( ApplyHom g (IntertwinerHom g r r) r,
    VectorSpace (RepToSectors g r),
    Scalar (RepToSectors g r) ~ ℂ
  ) =>
  Intertwiner g r r ->
  RepToSectors g r -+> RepToSectors g r
intertwinerEndoSectors (MkIntertwiner hom) =
  linearFunction (applyHom @g @(IntertwinerHom g r r) @r hom)

--------------------------------------------------------------------------------
-- SU(2)
--------------------------------------------------------------------------------

instance
  ( KnownNat j,
    ApplySectorC n n (IrrepDim SU2 j)
  ) =>
  ApplyHom SU2 '[ '(j, n, n)] '[ '(j, n)]
  where
  applyHom (InterCons blk InterNil) src =
    applySector @n @n @(IrrepDim SU2 j) blk src

instance
  ( KnownNat j,
    ApplySectorC n n (IrrepDim SU2 j),
    ApplyHom SU2 rest (s ': ss)
  ) =>
  ApplyHom SU2 ('(j, n, n) ': rest) ('(j, n) ': s ': ss)
  where
  applyHom (InterCons blk homRest) (srcHead, srcRest) =
    ( applySector @n @n @(IrrepDim SU2 j) blk srcHead,
      applyHom @SU2 @rest @(s ': ss) homRest srcRest
    )

--------------------------------------------------------------------------------
-- U(1)
--------------------------------------------------------------------------------

instance
  (ApplySectorC n n (IrrepDim U1 z)) =>
  ApplyHom U1 '[ '(z, n, n)] '[ '(z, n)]
  where
  applyHom (InterCons blk InterNil) src =
    applySector @n @n @(IrrepDim U1 z) blk src

instance
  ( ApplySectorC n n (IrrepDim U1 z),
    ApplyHom U1 rest (s ': ss)
  ) =>
  ApplyHom U1 ('(z, n, n) ': rest) ('(z, n) ': s ': ss)
  where
  applyHom (InterCons blk homRest) (srcHead, srcRest) =
    ( applySector @n @n @(IrrepDim U1 z) blk srcHead,
      applyHom @U1 @rest @(s ': ss) homRest srcRest
    )
