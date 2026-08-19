{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | U(1) examples for the group-indexed forgetful category ('Representations.Mor').
module Representations.Example.U1Example
  ( module Representations.Mor,
    example,
    example2,
    example3,
    example4,
    exampleFuseMult,
    exampleFuseMultMap,
  )
where

import Control.Category.Constrained (Category (..))
import Math.LinearMap.Asserted (type (-+>))
import Math.LinearMap.Category (type (⊗))
import Numeric.LinearAlgebra.Static (C, konst)
import Representations.Group (Group (U1))
import Representations.Intertwiner
  ( Intertwiner (..),
    IntertwinerSectors (..),
  )
import Representations.Mor
import Representations.Rep.Obj (RepObj (..), type Of)
import Representations.Rep.Tensor (Tensor)
import Representations.Utils (Z (..))
import Prelude hiding (id, (.))

example :: 'REP '[1 `Of` Pos 2] -&> 'REP '[2 `Of` Pos 2]
example = RepInter (MkIntertwiner (InterCons (konst 1) InterNil))

example2 :: C 1 -+> C 2
example2 = fmap' example

example3 :: ('REP '[1 `Of` Pos 1] ':⊗: 'REP '[1 `Of` Pos 1]) -&> 'REP '[2 `Of` Pos 2]
example3 = example . Fuse

example4 :: (C 1 ⊗ C 1) -+> C 2
example4 = fmap' example3

-- | Multiplicity: @C 2 ⊗ C 1 → C 2@ via general U(1) fuse.
exampleFuseMult ::
  ('REP '[2 `Of` Pos 1] ':⊗: 'REP '[1 `Of` Pos 0])
    -&> 'REP (Tensor U1 '[2 `Of` Pos 1] '[1 `Of` Pos 0])
exampleFuseMult = Fuse

exampleFuseMultMap :: (C 2 ⊗ C 1) -+> C 2
exampleFuseMultMap = fmap' exampleFuseMult
