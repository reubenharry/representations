{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}

-- | Group-indexed representation objects for the forgetful functor.
--
-- @'I@ is the monoidal unit (@C 1@); @'REP r@ is a reduced spine; @a ':⊗: b@
-- is the unfused external tensor product (not yet regrouped by total charge /
-- CG). Sector pairs are @m × j@ or @m `Of` j@ (same as @'(j, m)@).
--
-- Note: infix data constructors must start with @:@, so the product is
-- @(:⊗:)@ rather than bare @⊗@ (which would also clash visually with the
-- vector-space operator from 'Math.LinearMap.Category').
module Representations.Rep.Obj
  ( RepObj (..),
    ToVector,
    SectorVec,
    RepToSectors,
    ToSectors,
    RepAppend,
    type Of,
    type (×),
    type (⊕),
  )
where

import Data.Kind (Type)
import GHC.TypeLits (Nat)
import Math.LinearMap.Category (type (⊗))
import Numeric.LinearAlgebra.Static (C)
import Representations.Group (Group (..), IrrepDim, Irreps, Rep, RepDim)
import Representations.Utils (Z)

-- | Object of the rep category: unit, reduced spine, or nested unfused product.
data RepObj (g :: Group) where
  I :: RepObj g
  REP :: Rep g -> RepObj g
  (:⊗:) :: RepObj g -> RepObj g -> RepObj g

-- | @m `Of` j@ ≡ multiplicity @m@ of irrep @j@ (flips @'(j, m)@).
type (m :: Nat) `Of` j = '(j, m)

-- | Unicode alias: @m × j@ (read as multiplicity × irrep). Not @⊗@ — that is
-- the vector-space / monoidal product elsewhere in this library.
type (m :: Nat) × j = m `Of` j

infixl 7 ×

-- | Append two reduced spines (direct sum).
type family RepAppend (g :: Group) (xs :: Rep g) (ys :: Rep g) :: Rep g where
  RepAppend U1 '[] ys = ys
  RepAppend U1 (x ': xs) ys = x ': RepAppend U1 xs ys
  RepAppend SU2 '[] ys = ys
  RepAppend SU2 (x ': xs) ys = x ': RepAppend SU2 xs ys

-- | Combine irrep sectors into a spine, e.g.
-- @'(2 × SpinZero) ⊕ (1 × SpinOne)@.
-- Nested @⊕@ builds longer spines (@infixr 7@).
type family (⊕) (a :: k) (b :: l) :: Rep g where
  -- U(1): irrep labels are 'Z'
  (⊕) (a :: (Z, Nat)) (b :: (Z, Nat)) = '[a, b]
  (⊕) (a :: Rep U1) (b :: (Z, Nat)) = RepAppend U1 a '[b]
  (⊕) (a :: (Z, Nat)) (b :: Rep U1) = a ': b
  (⊕) (a :: Rep U1) (b :: Rep U1) = RepAppend U1 a b
  -- SU(2): irrep labels are @Nat@ (doubled spin)
  (⊕) (a :: (Nat, Nat)) (b :: (Nat, Nat)) = '[a, b]
  (⊕) (a :: Rep SU2) (b :: (Nat, Nat)) = RepAppend SU2 a '[b]
  (⊕) (a :: (Nat, Nat)) (b :: Rep SU2) = a ': b
  (⊕) (a :: Rep SU2) (b :: Rep SU2) = RepAppend SU2 a b

infixr 7 ⊕

-- | Image of the forgetful functor (group-indexed).
type family ToVector (g :: Group) (o :: RepObj g) :: Type where
  ToVector g 'I = C 1
  ToVector g ('REP r) = C (RepDim g r)
  ToVector g (a ':⊗: b) = ToVector g a ⊗ ToVector g b

-- | One isotypical summand: multiplicity ⊗ irrep.
-- Matches @fuseSU2Flat@ / @su2ExpandBlock@ (@kron(coeff, I_j)@, 2nd factor fastest).
type family SectorVec (g :: Group) (j :: Irreps g) (m :: Nat) :: Type where
  SectorVec g j m = C m ⊗ C (IrrepDim g j)

-- | Spine-level biproduct of 'SectorVec's. Case-split on @g@ so @Rep g@
-- reduces (non-injective). Last sector is not paired with @()@; @'[]@ unmatched.
type family RepToSectors (g :: Group) (r :: Rep g) :: Type where
  RepToSectors U1 '[ '(z, m)] = SectorVec U1 z m
  RepToSectors U1 ('(z, m) ': rs) = (SectorVec U1 z m, RepToSectors U1 rs)
  RepToSectors SU2 '[ '(j, m)] = SectorVec SU2 j m
  RepToSectors SU2 ('(j, m) ': rs) = (SectorVec SU2 j m, RepToSectors SU2 rs)

-- | Direct-sum-preserving forgetful image (sibling of 'ToVector').
type family ToSectors (g :: Group) (o :: RepObj g) :: Type where
  ToSectors g 'I = C 1
  ToSectors g (a ':⊗: b) = ToSectors g a ⊗ ToSectors g b
  ToSectors g ('REP r) = RepToSectors g r
