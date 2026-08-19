{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}
-- Extra imports keep 'Nat' in scope the way singletons' Demote expects
-- (ChargeEq's genSingletons splice).
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Representations.Utils
  ( Z (..),
    Add,
    AddPosNeg,
    Sub,
    vec,
    mat,
  )
where

import Data.AdditiveGroup (AdditiveGroup)
import Data.Data (Proxy (..))
import Data.IndexedListLiterals (IndexedListLiterals)
import Data.Kind (Constraint, Type)
import Data.VectorSpace (AdditiveGroup (..))
import GHC.TypeLits
import Linear.V (V)
import Math.LinearMap.Category (DimensionAware (..))
import Numeric.LinearAlgebra.Static (C, M, Sized (..))
import qualified Data.Vector.Sized as VSized

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

type family
  AddPosNeg
    (o :: Ordering)
    (a :: Nat)
    (b :: Nat) ::
    Z
  where
  AddPosNeg 'EQ a b =
    'Zero
  AddPosNeg 'GT a b =
    'Pos (Sub a b)
  AddPosNeg 'LT a b =
    'Neg (Sub b a)

-- | Build a static complex vector from a literal tuple, e.g. @vec (1,2) :: C 2@.
vec
  :: (Sized t c d, IndexedListLiterals a n t, KnownNat n, c ~ C n)
  => a -> c
vec a = (fromList . VSized.toList . VSized.fromTuple) a

-- | Build a static complex matrix from a literal tuple (row-major), e.g.
-- @mat (1,2,3,4) :: M 2 2@.
mat
  :: ( Sized t (M m n) d
     , IndexedListLiterals a (m * n) t
     , KnownNat m
     , KnownNat n
     , KnownNat (m * n)
     )
  => a -> M m n
mat a = fromList (VSized.toList (VSized.fromTuple a))
