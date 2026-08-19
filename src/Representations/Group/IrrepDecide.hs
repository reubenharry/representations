{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- | Singleton-level irrep equality, indexed by 'Group'.
module Representations.Group.IrrepDecide
  ( IrrepEqResult (..),
    IrrepDecide (..),
  )
where

import Data.Singletons (Sing)
import Representations.Group (Group (..), IrrepEq, Irreps)
import Representations.Group.ChargeEq (NatEqResult (..), ZEqResult (..), sNatEq, sZEq)

data IrrepEqResult (g :: Group) (a :: Irreps g) (b :: Irreps g) where
  IrrepEqTrue :: (IrrepEq g a b ~ 'True) => IrrepEqResult g a b
  IrrepEqFalse :: (IrrepEq g a b ~ 'False) => IrrepEqResult g a b

class IrrepDecide (g :: Group) where
  sIrrepEq :: Sing (a :: Irreps g) -> Sing (b :: Irreps g) -> IrrepEqResult g a b

instance IrrepDecide U1 where
  sIrrepEq sa sb =
    case sZEq sa sb of
      ZEqTrue -> IrrepEqTrue
      ZEqFalse -> IrrepEqFalse

instance IrrepDecide SU2 where
  sIrrepEq sa sb =
    case sNatEq sa sb of
      NatEqTrue -> IrrepEqTrue
      NatEqFalse -> IrrepEqFalse
