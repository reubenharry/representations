{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Shared group index for representation spines and intertwiner plumbing.
--
-- @GroupElement SU2@ is the Cayley–Klein type from 'Representations.Group.SU2'; the irrep
-- action lives there as 'Representations.Group.SU2.applyWigner'.
module Representations.Group
  ( Group (..)
  , GroupElement
  , SU2Element
  , Irreps
  , Rep
  , IrrepDim
  , SectorDim
  , RepDim
  , IrrepEq
  , LookupMultGo
  , LookupMult
  , HomSectorList
  , IntertwinerHom
  ) where

import Data.Kind (Type)
import GHC.TypeLits (Nat, type (+), type (*))
import Representations.Group.ChargeEq (NatEq, ZEq)
import Representations.Group.SU2 (SU2Element)
import Representations.Utils (Z, Append)

data Group = U1 | SU2

-- | Concrete group element used by representation actions.
type family GroupElement (g :: Group) :: Type where
  GroupElement U1 = Double
  GroupElement SU2 = SU2Element

type family Irreps (g :: Group) = (r :: Type) | r -> g where
  Irreps U1 = Z
  Irreps SU2 = Nat

type family Rep (g :: Group) = (r :: Type) | r -> g where
  Rep U1 = [(Z, Nat)]
  Rep SU2 = [(Nat, Nat)]

type family IrrepDim (g :: Group) (j :: Irreps g) :: Nat where
  IrrepDim U1 _ = 1
  IrrepDim SU2 j = j + 1

type family SectorDim (g :: Group) (j :: Irreps g) (m :: Nat) :: Nat where
  SectorDim U1 _ m = m
  SectorDim SU2 j m = m * (j + 1)

type family RepDim (g :: Group) (r :: Rep g) :: Nat where
  RepDim U1 '[] = 0
  RepDim U1 ('(z, m) ': rs) = m + RepDim U1 rs
  RepDim SU2 '[] = 0
  RepDim SU2 ('(j, m) ': rs) = m * (j + 1) + RepDim SU2 rs

type family IrrepEq (g :: Group) (a :: Irreps g) (b :: Irreps g) :: Bool where
  IrrepEq U1 a b = ZEq a b
  IrrepEq SU2 a b = NatEq a b

type family LookupMultGo (eq :: Bool) (m :: Nat) (rest :: Maybe Nat) :: Maybe Nat where
  LookupMultGo 'True m _ = 'Just m
  LookupMultGo 'False _ rest = rest

--------------------------------------------------------------------------------
-- Spine operations (case on @g@ first so @Rep g@ reduces)
--------------------------------------------------------------------------------

type family LookupMult (g :: Group) (j :: Irreps g) (q :: Rep g) :: Maybe Nat where
  LookupMult U1 _ '[]                = 'Nothing
  LookupMult U1 z ('(z2, m) ': rest) =
    LookupMultGo (ZEq z z2) m (LookupMult U1 z rest)
  LookupMult SU2 _ '[]                = 'Nothing
  LookupMult SU2 j ('(j2, m) ': rest) =
    LookupMultGo (NatEq j j2) m (LookupMult SU2 j rest)

type family MkBlock (j :: k) (mm :: Maybe Nat) (n :: Nat) :: [(k, Nat, Nat)] where
  MkBlock _ 'Nothing  _ = '[]
  MkBlock j ('Just m) n = '[ '( j, m, n)]

type family HomSectorList (g :: Group) (r :: Rep g) (q :: Rep g)
  :: [(Irreps g, Nat, Nat)] where
  HomSectorList U1 '[] _              = '[]
  HomSectorList U1 ('(z, n) ': rs) q  =
    Append (MkBlock z (LookupMult U1 z q) n) (HomSectorList U1 rs q)
  HomSectorList SU2 '[] _              = '[]
  HomSectorList SU2 ('(j, n) ': rs) q  =
    Append (MkBlock j (LookupMult SU2 j q) n) (HomSectorList SU2 rs q)

-- | Hom-sector spine for an intertwiner.
type IntertwinerHom (g :: Group) (r :: Rep g) (q :: Rep g) =
  HomSectorList g r q
