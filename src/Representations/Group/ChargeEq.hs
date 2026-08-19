{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}
-- The singletons (@SZero@\/@SPos@\/@SNeg@, @SingI@\/@SDecide@) for 'Z' are
-- orphans here because 'Z' is defined in "Utils"; collecting them in this one
-- small module — alongside the equality machinery that uses them — is
-- deliberate, so we silence the warning rather than scatter them.
{-# OPTIONS_GHC -Wno-orphans -Wno-unused-top-binds #-}

-- | Decidable equality for charges ('Z') and naturals, at both the type level
-- (the 'ZEq' \/ 'NatEq' families) and the singleton level (the @s*@ deciders
-- and reflexivity lemmas).
--
-- The deciders return /reduction witnesses/ ('ZEqResult', 'NatEqResult') rather
-- than plain 'Bool's: pattern-matching one brings a @ZEq z z2 ~ 'True@ (or
-- @'False@) equation into scope. This is what lets value-level singleton
-- recursion drive type-family reduction — GHC reduces a family on a known
-- @'True@\/@'False@, but never on charge /apartness/. So we phrase 'LookupMult'
-- and friends as a branch on 'ZEq' and decide that branch here.
module Representations.Group.ChargeEq
  ( -- * Type-level equality
    NatEq,
    ZEq,

    -- * Singleton-level deciders
    NatEqResult (..),
    sNatEq,
    ZEqResult (..),
    sZEq,
    fromNatEq,

    -- * Reflexivity
    natEqRefl,
    zEqRefl,
    chargeInteger,
  )
where

import Data.Proxy (Proxy (..))
import Data.Singletons (Sing, fromSing)
import Data.Singletons.TH (genSingletons, singDecideInstances)
import Data.Type.Equality ((:~:) (..))
import Data.Type.Ord (OrdCond, OrderingI (..))
import GHC.TypeLits (CmpNat, Nat)
import qualified GHC.TypeNats
import Representations.Utils (Z (..))

-- Charge singletons (@SZero@, @SPos@, @SNeg@) and @SDecide Z@ (used downstream by
-- the @(%~)@ charge comparison in composition).
$(genSingletons [''Z])
$(singDecideInstances [''Z])

--------------------------------------------------------------------------------
-- Type-level equality
--------------------------------------------------------------------------------

-- | Equality of charges as a @Bool@ (so families can branch on the result
-- instead of on a non-linear pattern). 'NatEq' is 'OrdCond' on 'CmpNat' —
-- stock @Data.Type.Equality.(==)@ on 'Nat' does not reduce for distinct
-- variables. 'ZEq' compares charges constructor-wise.
type family NatEq (a :: Nat) (b :: Nat) :: Bool where
  NatEq a b = OrdCond (CmpNat a b) 'False 'True 'False

type family ZEq (a :: Z) (b :: Z) :: Bool where
  ZEq 'Zero 'Zero = 'True
  ZEq ('Pos a) ('Pos b) = NatEq a b
  ZEq ('Neg a) ('Neg b) = NatEq a b
  ZEq _ _ = 'False

--------------------------------------------------------------------------------
-- Singleton-level deciders
--------------------------------------------------------------------------------

-- | A decided @NatEq@, carrying the resulting reduction equation.
data NatEqResult (a :: Nat) (b :: Nat) where
  NatEqTrue :: (NatEq a b ~ 'True) => NatEqResult a b
  NatEqFalse :: (NatEq a b ~ 'False) => NatEqResult a b

-- | Decide 'NatEq' via GHC's primitive 'GHC.TypeNats.cmpNat', whose 'OrderingI'
-- result exposes the @CmpNat@ equation 'OrdCond' collapses to a 'Bool'.
sNatEq :: forall a b. Sing (a :: Nat) -> Sing (b :: Nat) -> NatEqResult a b
sNatEq sa sb =
  GHC.TypeNats.withKnownNat sa $
    GHC.TypeNats.withKnownNat sb $
      case GHC.TypeNats.cmpNat (Proxy @a) (Proxy @b) of
        EQI -> NatEqTrue -- CmpNat a b ~ 'EQ ⟹ NatEq a b = 'True
        LTI -> NatEqFalse -- CmpNat a b ~ 'LT ⟹ NatEq a b = 'False
        GTI -> NatEqFalse -- CmpNat a b ~ 'GT ⟹ NatEq a b = 'False

-- | A decided @ZEq@, carrying the resulting reduction equation.
data ZEqResult (z :: Z) (z2 :: Z) where
  ZEqTrue :: (ZEq z z2 ~ 'True) => ZEqResult z z2
  ZEqFalse :: (ZEq z z2 ~ 'False) => ZEqResult z z2

-- | Decide 'ZEq' by structural recursion on the charge singletons, delegating to
-- 'sNatEq' for matching @Pos@\/@Neg@ payloads.
sZEq :: Sing (z :: Z) -> Sing (z2 :: Z) -> ZEqResult z z2
sZEq SZero SZero = ZEqTrue
sZEq (SPos a) (SPos b) = fromNatEq (sNatEq a b)
sZEq (SNeg a) (SNeg b) = fromNatEq (sNatEq a b)
sZEq SZero (SPos _) = ZEqFalse
sZEq SZero (SNeg _) = ZEqFalse
sZEq (SPos _) SZero = ZEqFalse
sZEq (SPos _) (SNeg _) = ZEqFalse
sZEq (SNeg _) SZero = ZEqFalse
sZEq (SNeg _) (SPos _) = ZEqFalse

-- | Lift a @NatEq@ witness to the @ZEq@ of the surrounding charge (they share the
-- same @'True'@\/@'False'@ payload for @Pos@\/@Neg@).
fromNatEq :: (ZEq z z2 ~ NatEq a b) => NatEqResult a b -> ZEqResult z z2
fromNatEq NatEqTrue = ZEqTrue
fromNatEq NatEqFalse = ZEqFalse

--------------------------------------------------------------------------------
-- Reflexivity
--------------------------------------------------------------------------------

-- | @NatEq@ is reflexive. GHC's built-in solver knows @CmpNat a a ~ 'EQ@, so the
-- @LTI@\/@GTI@ branches have contradictory givens and need no equations.
natEqRefl :: forall a. Sing (a :: Nat) -> NatEq a a :~: 'True
natEqRefl sa =
  GHC.TypeNats.withKnownNat sa $
    case GHC.TypeNats.cmpNat (Proxy @a) (Proxy @a) of
      EQI -> Refl

-- | @ZEq@ is reflexive — the witness for "a charge is present in its own rep".
zEqRefl :: Sing (z :: Z) -> ZEq z z :~: 'True
zEqRefl SZero = Refl
zEqRefl (SPos a) = natEqRefl a
zEqRefl (SNeg a) = natEqRefl a

-- | Total order key for U(1) charge singletons.
chargeInteger :: Sing (z :: Z) -> Integer
chargeInteger SZero = 0
chargeInteger (SPos sn) = fromIntegral (fromSing sn)
chargeInteger (SNeg sn) = negate (fromIntegral (fromSing sn))
