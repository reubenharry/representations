{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | U(1) examples for the group-indexed forgetful category ('Representations.Mor').
module Representations.Example.U1Example
  ( module Representations.Mor
  , example
  , example2
  , example3
  , example4
  , exampleFuseMult
  , exampleFuseMultMap
  ) where

import Prelude hiding ((.), id)
import Control.Category.Constrained (Category (..))
import Math.LinearMap.Category (type (⊗))
import Math.LinearMap.Asserted (type (-+>))
import Numeric.LinearAlgebra.Static (C, konst)
import Representations.Intertwiner
  ( Intertwiner (..), IntertwinerSectors (..) )
import Representations.Group (Group (U1))
import Representations.Rep.HomBlock (CoeffBlock (..))
import Representations.Mor
import Representations.Rep.Obj (RepObj (..), type IrrepOf)
import Representations.Rep.Tensor (Tensor)
import Representations.Utils (Z (..))

example :: 'REP '[ 1 `IrrepOf` Pos 2] -&> 'REP '[ 2 `IrrepOf` Pos 2]
example = RepInter (MkIntertwiner (InterCons (CoeffBlock (konst 1)) InterNil))

example2 :: C 1 -+> C 2
example2 = fmap' example

example3 :: ('REP '[ 1 `IrrepOf` Pos 1] ':⊗: 'REP '[ 1 `IrrepOf` Pos 1]) -&> 'REP '[ 2 `IrrepOf` Pos 2]
example3 = example . Fuse

example4 :: (C 1 ⊗ C 1) -+> C 2
example4 = fmap' example3

-- | Multiplicity: @C 2 ⊗ C 1 → C 2@ via general U(1) fuse.
exampleFuseMult
  :: ('REP '[ 2 `IrrepOf` Pos 1] ':⊗: 'REP '[ 1 `IrrepOf` Pos 0])
     -&> 'REP (Tensor U1 '[ 2 `IrrepOf` Pos 1] '[ 1 `IrrepOf` Pos 0])
exampleFuseMult = Fuse

exampleFuseMultMap :: (C 2 ⊗ C 1) -+> C 2
exampleFuseMultMap = fmap' exampleFuseMult
