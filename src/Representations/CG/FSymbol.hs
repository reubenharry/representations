{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | F-symbols as @Intertwiner@ between coalesced @Tensor@ parenthesizations.
--
-- * __U(1):__ coalesce+sort makes both spines match; F is @eye@ on each
--   multiplicity block.
-- * __SU(2):__ Schur blocks of @fuseTreeR ∘ fuseTreeL⁻¹@. Nested
--   second-factor-fastest flats make Vec @Assoc@ the identity, so this is the
--   fused associator matching 'fuseSU2Flat'. (Racah \/ 6j equivalent; closed
--   form can replace the dense step later without changing the API.)
module Representations.CG.FSymbol
  ( PackSchur (..),
    fSymbolHomU1,
    fSymbolHomU1Inv,
    fSymbolHomSU2,
    fSymbolHomSU2Inv,
  )
where

import Control.Monad.ST (runST)
import Data.Complex (Complex (..))
import Data.Proxy (Proxy (..))
import qualified Data.Vector.Storable as VS
import qualified Data.Vector.Storable.Mutable as MVS
import GHC.TypeLits (KnownNat, Nat, natVal)
import qualified Numeric.LinearAlgebra as HM
import Numeric.LinearAlgebra.Static
  ( M,
    Sized (fromList),
  )
import Representations.CG.SU2 (fuseSU2Flat, repDimOf, sectorsSU2)
import Representations.Group
  ( Group (..),
    IntertwinerHom,
  )
import Representations.Intertwiner (BuildIdHom (..), Intertwiner (..), IntertwinerSectors (..))
import Representations.Rep.HomBlock (HomBlockDim)
import Representations.Rep.Singleton (KnownRep (..), SRep)
import Representations.Rep.Tensor (Tensor)

type ℂ = Complex Double

--------------------------------------------------------------------------------
-- U(1) F is identity on coalesced spines
--------------------------------------------------------------------------------

fSymbolHomU1 ::
  forall r q s.
  ( KnownRep U1 r,
    KnownRep U1 q,
    KnownRep U1 s,
    KnownRep U1 (Tensor U1 (Tensor U1 r q) s),
    KnownRep U1 (Tensor U1 r (Tensor U1 q s)),
    BuildIdHom
      U1
      ( IntertwinerHom
          U1
          (Tensor U1 (Tensor U1 r q) s)
          (Tensor U1 r (Tensor U1 q s))
      )
  ) =>
  Proxy r ->
  Proxy q ->
  Proxy s ->
  Intertwiner
    U1
    (Tensor U1 (Tensor U1 r q) s)
    (Tensor U1 r (Tensor U1 q s))
fSymbolHomU1 _ _ _ =
  MkIntertwiner
    ( idHom @U1
        @( IntertwinerHom
             U1
             (Tensor U1 (Tensor U1 r q) s)
             (Tensor U1 r (Tensor U1 q s))
         )
    )

fSymbolHomU1Inv ::
  forall r q s.
  ( KnownRep U1 r,
    KnownRep U1 q,
    KnownRep U1 s,
    KnownRep U1 (Tensor U1 (Tensor U1 r q) s),
    KnownRep U1 (Tensor U1 r (Tensor U1 q s)),
    BuildIdHom
      U1
      ( IntertwinerHom
          U1
          (Tensor U1 r (Tensor U1 q s))
          (Tensor U1 (Tensor U1 r q) s)
      )
  ) =>
  Proxy r ->
  Proxy q ->
  Proxy s ->
  Intertwiner
    U1
    (Tensor U1 r (Tensor U1 q s))
    (Tensor U1 (Tensor U1 r q) s)
fSymbolHomU1Inv _ _ _ =
  MkIntertwiner
    ( idHom @U1
        @( IntertwinerHom
             U1
             (Tensor U1 r (Tensor U1 q s))
             (Tensor U1 (Tensor U1 r q) s)
         )
    )

--------------------------------------------------------------------------------
-- SU(2) triple fusion trees on flat buffers
--------------------------------------------------------------------------------

-- | @((r⊗q)⊗s)@ product flat → coalesced @Tensor (Tensor r q) s@.
fuseTreeLeft ::
  SRep SU2 r ->
  SRep SU2 q ->
  SRep SU2 s ->
  SRep SU2 rq ->
  VS.Vector ℂ ->
  VS.Vector ℂ
fuseTreeLeft sr sq ss srq vin =
  let dr = repDimOf (sectorsSU2 sr)
      dq = repDimOf (sectorsSU2 sq)
      ds = repDimOf (sectorsSU2 ss)
      dimRQ = dr * dq
      dimRqF = VS.length (fuseSU2Flat sr sq (VS.replicate dimRQ 0))
      mid = runST $ do
        m <- MVS.new (dimRqF * ds)
        mapM_
          ( \iS -> do
              let fiber =
                    VS.generate dimRQ $ \iRq ->
                      vin VS.! (iRq * ds + iS)
                  fused = fuseSU2Flat sr sq fiber
              mapM_
                ( \iRq' ->
                    MVS.write m (iRq' * ds + iS) (fused VS.! iRq')
                )
                [0 .. dimRqF - 1]
          )
          [0 .. ds - 1]
        VS.freeze m
   in fuseSU2Flat srq ss mid

-- | @(r⊗(q⊗s))@ product flat → coalesced @Tensor r (Tensor q s)@.
-- Product flat layout coincides with left-associated nesting (Assoc = id).
fuseTreeRight ::
  SRep SU2 r ->
  SRep SU2 q ->
  SRep SU2 s ->
  SRep SU2 qs ->
  VS.Vector ℂ ->
  VS.Vector ℂ
fuseTreeRight sr sq ss sqs vin =
  let dr = repDimOf (sectorsSU2 sr)
      dq = repDimOf (sectorsSU2 sq)
      ds = repDimOf (sectorsSU2 ss)
      dimQS = dq * ds
      dimQsF = VS.length (fuseSU2Flat sq ss (VS.replicate dimQS 0))
      mid = runST $ do
        m <- MVS.new (dr * dimQsF)
        mapM_
          ( \iR -> do
              let fiber =
                    VS.generate dimQS $ \iQs ->
                      vin VS.! (iR * dimQS + iQs)
                  fused = fuseSU2Flat sq ss fiber
              mapM_
                ( \iQs' ->
                    MVS.write m (iR * dimQsF + iQs') (fused VS.! iQs')
                )
                [0 .. dimQsF - 1]
          )
          [0 .. dr - 1]
        VS.freeze m
   in fuseSU2Flat sr sqs mid

matFromMap :: Int -> Int -> (VS.Vector ℂ -> VS.Vector ℂ) -> HM.Matrix ℂ
matFromMap _nRows nCols f =
  HM.fromColumns
    [ VS.convert (f (e i))
    | i <- [0 .. nCols - 1]
    ]
  where
    e i = VS.generate nCols $ \j -> if i == j then 1 else 0

-- | Dense F: left fused → right fused.
denseFMove ::
  SRep SU2 r ->
  SRep SU2 q ->
  SRep SU2 s ->
  SRep SU2 rq ->
  SRep SU2 qs ->
  SRep SU2 left ->
  SRep SU2 right ->
  HM.Matrix ℂ
denseFMove sr sq ss srq sqs sLeft sRight =
  let dr = repDimOf (sectorsSU2 sr)
      dq = repDimOf (sectorsSU2 sq)
      ds = repDimOf (sectorsSU2 ss)
      dimP = dr * dq * ds
      dimL = repDimOf (sectorsSU2 sLeft)
      dimR = repDimOf (sectorsSU2 sRight)
      mL = matFromMap dimL dimP (fuseTreeLeft sr sq ss srq)
      mR = matFromMap dimR dimP (fuseTreeRight sr sq ss sqs)
   in mR HM.<> HM.tr mL

--------------------------------------------------------------------------------
-- Pack dense F into Schur blocks along IntertwinerHom
--------------------------------------------------------------------------------

class PackSchur (hom :: [(Nat, Nat, Nat)]) where
  packSchur ::
    [(Int, Int, Int)] -> -- domain sectors
    [(Int, Int, Int)] -> -- codomain sectors
    HM.Matrix ℂ -> -- rows = codomain, cols = domain
    IntertwinerSectors SU2 hom

instance PackSchur '[] where
  packSchur _ _ _ = InterNil

instance
  ( KnownNat m,
    KnownNat n,
    KnownNat j,
    KnownNat (HomBlockDim m n),
    PackSchur rest
  ) =>
  PackSchur ('(j, m, n) ': rest)
  where
  packSchur domainSecs codomainSecs mat =
    let tj = fromIntegral (natVal (Proxy @j))
        mV = fromIntegral (natVal (Proxy @m))
        nV = fromIntegral (natVal (Proxy @n))
        d = tj + 1
        (offDom, _) = sectorOffset tj domainSecs
        (offCod, _) = sectorOffset tj codomainSecs
        blk = extractKronEye mV nV d mat offCod offDom
     in InterCons blk (packSchur @rest domainSecs codomainSecs mat)

sectorOffset :: Int -> [(Int, Int, Int)] -> (Int, Int)
sectorOffset tj secs =
  case [(off, mult) | (t, mult, off) <- secs, t == tj] of
    (p : _) -> p
    [] -> error $ "PackSchur: missing sector tj=" ++ show tj

extractKronEye ::
  forall m n.
  (KnownNat m, KnownNat n, KnownNat (HomBlockDim m n)) =>
  Int ->
  Int ->
  Int ->
  HM.Matrix ℂ ->
  Int ->
  Int ->
  M m n
extractKronEye mV nV d mat offCod offDom =
  let entries =
        [ mat `HM.atIndex` (offCod + a * d, offDom + b * d)
        | a <- [0 .. mV - 1],
          b <- [0 .. nV - 1]
        ]
   in fromList entries

fSymbolHomSU2 ::
  forall r q s.
  ( KnownRep SU2 r,
    KnownRep SU2 q,
    KnownRep SU2 s,
    KnownRep SU2 (Tensor SU2 r q),
    KnownRep SU2 (Tensor SU2 q s),
    KnownRep SU2 (Tensor SU2 (Tensor SU2 r q) s),
    KnownRep SU2 (Tensor SU2 r (Tensor SU2 q s)),
    PackSchur
      ( IntertwinerHom
          SU2
          (Tensor SU2 (Tensor SU2 r q) s)
          (Tensor SU2 r (Tensor SU2 q s))
      )
  ) =>
  Proxy r ->
  Proxy q ->
  Proxy s ->
  Intertwiner
    SU2
    (Tensor SU2 (Tensor SU2 r q) s)
    (Tensor SU2 r (Tensor SU2 q s))
fSymbolHomSU2 _ _ _ =
  let sr = repSing @SU2 @r
      sq = repSing @SU2 @q
      ss = repSing @SU2 @s
      srq = repSing @SU2 @(Tensor SU2 r q)
      sqs = repSing @SU2 @(Tensor SU2 q s)
      sLeft = repSing @SU2 @(Tensor SU2 (Tensor SU2 r q) s)
      sRight = repSing @SU2 @(Tensor SU2 r (Tensor SU2 q s))
      mat = denseFMove sr sq ss srq sqs sLeft sRight
      hom =
        packSchur
          @( IntertwinerHom
               SU2
               (Tensor SU2 (Tensor SU2 r q) s)
               (Tensor SU2 r (Tensor SU2 q s))
           )
          (sectorsSU2 sLeft)
          (sectorsSU2 sRight)
          mat
   in MkIntertwiner hom

fSymbolHomSU2Inv ::
  forall r q s.
  ( KnownRep SU2 r,
    KnownRep SU2 q,
    KnownRep SU2 s,
    KnownRep SU2 (Tensor SU2 r q),
    KnownRep SU2 (Tensor SU2 q s),
    KnownRep SU2 (Tensor SU2 (Tensor SU2 r q) s),
    KnownRep SU2 (Tensor SU2 r (Tensor SU2 q s)),
    PackSchur
      ( IntertwinerHom
          SU2
          (Tensor SU2 r (Tensor SU2 q s))
          (Tensor SU2 (Tensor SU2 r q) s)
      )
  ) =>
  Proxy r ->
  Proxy q ->
  Proxy s ->
  Intertwiner
    SU2
    (Tensor SU2 r (Tensor SU2 q s))
    (Tensor SU2 (Tensor SU2 r q) s)
fSymbolHomSU2Inv _ _ _ =
  let sr = repSing @SU2 @r
      sq = repSing @SU2 @q
      ss = repSing @SU2 @s
      srq = repSing @SU2 @(Tensor SU2 r q)
      sqs = repSing @SU2 @(Tensor SU2 q s)
      sLeft = repSing @SU2 @(Tensor SU2 (Tensor SU2 r q) s)
      sRight = repSing @SU2 @(Tensor SU2 r (Tensor SU2 q s))
      mat = denseFMove sr sq ss srq sqs sLeft sRight
      matInv = HM.tr mat
      hom =
        packSchur
          @( IntertwinerHom
               SU2
               (Tensor SU2 r (Tensor SU2 q s))
               (Tensor SU2 (Tensor SU2 r q) s)
           )
          (sectorsSU2 sRight)
          (sectorsSU2 sLeft)
          matInv
   in MkIntertwiner hom
