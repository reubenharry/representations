{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | A runtime singleton for a representation spine @'Rep g'@ — a list of
-- @(irrep label, multiplicity)@ sectors. This is the value that label-keyed
-- recursions (composition, application) walk to drive type-family reduction.
--
-- Promoted list ops come from @singletons-base@; this spine is still bespoke
-- because it is group-indexed (so @Rep g@ reduces under matching) and carries
-- a @KnownNat@ multiplicity rather than a full @Sing m@.
module Representations.Rep.Singleton
  ( SRep (..),
    KnownRep (..),
  )
where

import Data.Singletons (Sing, SingI, sing)
import GHC.TypeLits (KnownNat)
import Representations.Group (Group (..), Rep)
import Representations.Group.ChargeEq ()

-- SingI instances for the U(1) charge kind Z

-- | The singleton for a rep spine: one 'Sing' irrep label and a 'KnownNat'
-- multiplicity per sector. Constructors are indexed by @g@ so @'Rep g'@ reduces
-- under pattern matching.
data SRep (g :: Group) (r :: Rep g) where
  SRepNilU1 :: SRep U1 '[]
  SRepNilSU2 :: SRep SU2 '[]
  SRepCons :: forall z m rs. (KnownNat m) => Sing z -> SRep U1 rs -> SRep U1 ('(z, m) ': rs)
  SRepConsSU2 :: forall j m rs. (KnownNat j, KnownNat m) => Sing j -> SRep SU2 rs -> SRep SU2 ('(j, m) ': rs)

-- | Materialize the 'SRep' singleton for a statically-known rep.
class KnownRep (g :: Group) (r :: Rep g) where
  repSing :: SRep g r

instance KnownRep U1 '[] where
  repSing = SRepNilU1

instance (SingI z, KnownNat m, KnownRep U1 rs) => KnownRep U1 ('(z, m) ': rs) where
  repSing = SRepCons (sing @z) (repSing @U1 @rs)

instance KnownRep SU2 '[] where
  repSing = SRepNilSU2

instance (SingI j, KnownNat j, KnownNat m, KnownRep SU2 rs) => KnownRep SU2 ('(j, m) ': rs) where
  repSing = SRepConsSU2 (sing @j) (repSing @SU2 @rs)
