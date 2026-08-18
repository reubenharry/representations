{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

-- | Monoidal product of linear maps, copied from the quantum repo's
-- @TensorNetwork.Categorical@ so this package does not depend on tensor
-- networks. Cleanup can fold this into a more natural home.
module Symmetry.Categorical
  ( (⊗^)
  ) where

import Math.LinearMap.Category
  ( LSpace, TensorSpace (..), type (+>), type (⊗)
  , tensorOfMaps, (-+$>)
  )
import Data.VectorSpace (Scalar)

-- | @(f ⊗^ g) $ (x ⊗ y) = (f $ x) ⊗ (g $ y)@
(⊗^)
  :: forall u v u' v'
   . ( LSpace u, LSpace u', LSpace v, LSpace v'
     , TensorSpace v, TensorSpace v'
     , TensorSpace (u ⊗ u'), TensorSpace (v ⊗ v')
     , Scalar u ~ Scalar u', Scalar u ~ Scalar v, Scalar v ~ Scalar v'
     )
  => (u +> v) -> (u' +> v') -> ((u ⊗ u') +> (v ⊗ v'))
f ⊗^ g = (tensorOfMaps -+$> f) -+$> g
infixr 7 ⊗^
