{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoStarIsType #-}
-- Extra imports keep 'Nat' in scope the way singletons' Demote expects
-- (ChargeEq's genSingletons splice).
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Representations.Utils
  ( Z (..)
  , Add
  , AddPosNeg
  , Sub
  , Scale
  , Append
  ) where


import Data.Kind (Type, Constraint)
import GHC.TypeLits
import Numeric.LinearAlgebra.Static (M, Sized (..), C)
import Linear.V (V)
import Data.AdditiveGroup (AdditiveGroup)
import Data.VectorSpace (AdditiveGroup(..))
import Math.LinearMap.Category (DimensionAware (..))
import Data.Data (Proxy(..))

--------------------------------------------------------------------------------
-- Integer type at the type level
--------------------------------------------------------------------------------

data Z
  = Neg Nat
  | Zero
  | Pos Nat

--------------------------------------------------------------------------------
-- Type-level integer arithmetic
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Nat subtraction assuming a >= b
--------------------------------------------------------------------------------

type family Sub (a :: Nat) (b :: Nat) :: Nat where
  Sub a 0 = a
  Sub a a = 0
  Sub a b = a - b

--------------------------------------------------------------------------------
-- Integer addition
--------------------------------------------------------------------------------

type family Add (a :: Z) (b :: Z) :: Z where

  Add 'Zero b = b
  Add a 'Zero = a

  Add ('Pos a) ('Pos b) =
    'Pos (a + b)

  Add ('Neg a) ('Neg b) =
    'Neg (a + b)

  Add ('Pos a) ('Neg b) =
    AddPosNeg (CmpNat a b) a b

  Add ('Neg a) ('Pos b) =
    AddPosNeg (CmpNat b a) b a

type family AddPosNeg
  (o :: Ordering)
  (a :: Nat)
  (b :: Nat)
  :: Z where

  AddPosNeg 'EQ a b =
    'Zero

  AddPosNeg 'GT a b =
    'Pos (Sub a b)

  AddPosNeg 'LT a b =
    'Neg (Sub b a)


-- One irrep sector with multiplicity
--
-- (charge, multiplicity)
--

type family Scale
  (m :: Nat)
  (n :: Nat)
  :: Nat where

  Scale m n = m  * n

type family Append (a :: [k]) (b :: [k]) :: [k] where
  Append '[] b = b
  Append (x ': xs) b = x ': Append xs b

