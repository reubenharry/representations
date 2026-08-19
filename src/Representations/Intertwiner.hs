{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}
-- The KnownNat solver discharges @KnownNat (m * n)@ (i.e. @KnownNat (HomBlockDim
-- m n)@) from @KnownNat m@ and @KnownNat n@. The charge-keyed @compose@
-- synthesizes blocks whose dimensions are existential (recovered from rep
-- singletons), so these products can't be solved from the literal types alone.
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Schur-block intertwiners indexed by group and representation spine.
module Representations.Intertwiner
  ( Intertwiner (..),
    IntertwinerSectors (..),
    compose,
    mkIdHom,
    intertwinerLinear,
    RepLookup (..),
    LookupResult (..),
    BuildIdHom (..),
    HasIntertwiner,
    targetIrrepOffset,
  )
where

import Control.Category.Constrained (Category (..))
import Data.Complex (Complex)
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (..))
import Data.Singletons (Sing)
import Data.Singletons.Decide (Decision (..), SDecide (..))
import Data.Type.Equality ((:~:) (..))
import GHC.Exts (IsList (..))
import qualified Data.Vector.Storable as V
import Data.VectorSpace (AdditiveGroup (..), VectorSpace (..))
import GHC.TypeLits (KnownNat, Nat, natVal)
import qualified GHC.TypeNats
import Math.LinearMap.Asserted (linearFunction, type (-+>))
import Numeric.LinearAlgebra.Static
  ( C,
    Domain (app),
    M,
    create,
    extract,
    konst,
  )
import Numeric.LinearAlgebra.Static.COrphans ()
import Representations.Group
  ( Group (..),
    IntertwinerHom,
    Irreps,
    LookupMult,
    Rep,
    RepDim,
    SectorDim,
  )
import Representations.Group.IrrepDecide (IrrepDecide (..), IrrepEqResult (..))
import Representations.Rep.HomBlock
  ( ExpandBlock (..),
    HomBlockDim,
    addBlock,
    composeBlock,
    eyeBlock,
    negateBlock,
    scaleBlock,
    zeroBlock,
  )
import Representations.Rep.Singleton (KnownRep (..), SRep (..))
import Prelude hiding ((.))
import qualified Prelude as P

--------------------------------------------------------------------------------
-- Group-indexed representation spine
--------------------------------------------------------------------------------

-- | Intertwiner data indexed by its hom-sector spine.
-- Blocks store @m × n@ scalar coefficients (Schur); @j@ appears in the
-- hom-spine index and drives @expandBlock @g @j@ at application time.
data IntertwinerSectors (g :: Group) (hom :: [(Irreps g, Nat, Nat)]) where
  InterNil :: IntertwinerSectors g '[]
  InterCons ::
    ( KnownNat m,
      KnownNat n,
      KnownNat (HomBlockDim m n)
    ) =>
    M m n ->
    IntertwinerSectors g rest ->
    IntertwinerSectors g ('(j, m, n) ': rest)

instance Show (IntertwinerSectors g hom) where
  show InterNil = "InterNil"
  show (InterCons block rest) =
    P.show block ++ " : " ++ P.show rest

-- | @OverloadedLists@ for empty and singleton hom spines (see also same-shape
-- multi-block instances below). Heterogeneous block sizes still need 'InterCons'.
-- Split by 'Group' because @Irreps g@ is a type family.
instance IsList (IntertwinerSectors U1 '[]) where
  type Item (IntertwinerSectors U1 '[]) = M 1 1
  fromList [] = InterNil
  fromList _ =
    error "IntertwinerSectors '[]: expected empty list"
  toList InterNil = []

instance IsList (IntertwinerSectors SU2 '[]) where
  type Item (IntertwinerSectors SU2 '[]) = M 1 1
  fromList [] = InterNil
  fromList _ =
    error "IntertwinerSectors '[]: expected empty list"
  toList InterNil = []

instance
  ( KnownNat m
  , KnownNat n
  , KnownNat (HomBlockDim m n)
  ) =>
  IsList (IntertwinerSectors U1 '[ '(j, m, n)])
  where
  type Item (IntertwinerSectors U1 '[ '(j, m, n)]) = M m n
  fromList [block] = InterCons block InterNil
  fromList _ =
    error "IntertwinerSectors singleton: expected exactly one block"
  toList (InterCons block InterNil) = [block]

instance
  ( KnownNat m
  , KnownNat n
  , KnownNat (HomBlockDim m n)
  ) =>
  IsList (IntertwinerSectors SU2 '[ '(j, m, n)])
  where
  type Item (IntertwinerSectors SU2 '[ '(j, m, n)]) = M m n
  fromList [block] = InterCons block InterNil
  fromList _ =
    error "IntertwinerSectors singleton: expected exactly one block"
  toList (InterCons block InterNil) = [block]

instance
  ( KnownNat m
  , KnownNat n
  , KnownNat (HomBlockDim m n)
  ) =>
  IsList
    (IntertwinerSectors U1 '[ '(j1, m, n), '(j2, m, n)])
  where
  type Item (IntertwinerSectors U1 '[ '(j1, m, n), '(j2, m, n)]) = M m n
  fromList [a, b] = InterCons a (InterCons b InterNil)
  fromList _ =
    error "IntertwinerSectors pair: expected exactly two blocks"
  toList (InterCons a (InterCons b InterNil)) = [a, b]

instance
  ( KnownNat m
  , KnownNat n
  , KnownNat (HomBlockDim m n)
  ) =>
  IsList
    (IntertwinerSectors SU2 '[ '(j1, m, n), '(j2, m, n)])
  where
  type Item (IntertwinerSectors SU2 '[ '(j1, m, n), '(j2, m, n)]) = M m n
  fromList [a, b] = InterCons a (InterCons b InterNil)
  fromList _ =
    error "IntertwinerSectors pair: expected exactly two blocks"
  toList (InterCons a (InterCons b InterNil)) = [a, b]

newtype Intertwiner (g :: Group) (r :: Rep g) (q :: Rep g) = MkIntertwiner
  { unIntertwiner :: IntertwinerSectors g (IntertwinerHom g r q)
  }
  deriving (Show) via (IntertwinerSectors g (IntertwinerHom g r q))

class BuildIdHom (g :: Group) (hom :: [(Irreps g, Nat, Nat)]) where
  idHom :: IntertwinerSectors g hom

instance BuildIdHom U1 '[] where
  idHom = InterNil

instance
  ( KnownNat m,
    KnownNat (HomBlockDim m m),
    BuildIdHom U1 rest
  ) =>
  BuildIdHom U1 ('(j, m, m) ': rest)
  where
  idHom = InterCons (eyeBlock @m) idHom

instance BuildIdHom SU2 '[] where
  idHom = InterNil

instance
  ( KnownNat m,
    KnownNat (HomBlockDim m m),
    BuildIdHom SU2 rest
  ) =>
  BuildIdHom SU2 ('(j, m, m) ': rest)
  where
  idHom = InterCons (eyeBlock @m) idHom

mkIdHom ::
  forall g a.
  (BuildIdHom g (IntertwinerHom g a a)) =>
  Intertwiner g a a
mkIdHom = MkIntertwiner idHom

class (IrrepDecide g) => RepLookup g where
  sLookupMult :: Sing (j :: Irreps g) -> SRep g (q :: Rep g) -> LookupResult g j q

data LookupResult (g :: Group) (j :: Irreps g) (q :: Rep g) where
  Absent ::
    (LookupMult g j q ~ 'Nothing) =>
    LookupResult g j q
  Present ::
    (LookupMult g j q ~ 'Just m, KnownNat m) =>
    Proxy m -> LookupResult g j q

instance RepLookup U1 where
  sLookupMult _ SRepNilU1 = Absent
  sLookupMult sz (SRepCons @z2 @m sz2 rest) =
    case sIrrepEq @U1 sz sz2 of
      IrrepEqTrue -> Present (Proxy @m)
      IrrepEqFalse -> case sLookupMult sz rest of
        Absent -> Absent
        Present pm -> Present pm

instance RepLookup SU2 where
  sLookupMult _ SRepNilSU2 = Absent
  sLookupMult sj (SRepConsSU2 @j2 @m sj2 rest) =
    case sIrrepEq @SU2 sj sj2 of
      IrrepEqTrue -> Present (Proxy @m)
      IrrepEqFalse -> case sLookupMult sj rest of
        Absent -> Absent
        Present pm -> Present pm

--------------------------------------------------------------------------------
-- Label-keyed view of a @b -> c@ intertwiner (for composition)
--------------------------------------------------------------------------------

data BCEntry (g :: Group) (c :: Rep g) where
  BCEntry ::
    forall g j src tgt c.
    (KnownNat src, KnownNat tgt, LookupMult g j c ~ 'Just tgt) =>
    Sing j -> M tgt src -> BCEntry g c

bcIndex ::
  forall g b c.
  (RepLookup g) =>
  SRep g b ->
  SRep g c ->
  IntertwinerSectors g (IntertwinerHom g b c) ->
  [BCEntry g c]
bcIndex SRepNilU1 _ InterNil = []
bcIndex SRepNilSU2 _ InterNil = []
bcIndex (SRepCons sbz brest) sc homBC =
  case sLookupMult @U1 sbz sc of
    Absent -> bcIndex brest sc homBC
    Present (_ :: Proxy pc) -> case homBC of
      InterCons blk rest -> BCEntry sbz blk : bcIndex brest sc rest
bcIndex (SRepConsSU2 sbj brest) sc homBC =
  case sLookupMult @SU2 sbj sc of
    Absent -> bcIndex brest sc homBC
    Present (_ :: Proxy pc) -> case homBC of
      InterCons blk rest -> BCEntry sbj blk : bcIndex brest sc rest

findBC ::
  forall g j c m p.
  ( SDecide (Irreps g),
    LookupMult g j c ~ 'Just p,
    KnownNat m,
    KnownNat p
  ) =>
  Sing j -> [BCEntry g c] -> M p m
findBC _ [] =
  error "findBC: b->c block absent (unreachable: label present in both b and c)"
findBC sj (BCEntry (sk :: Sing k) (blk :: M tgt src) : rest) =
  case sj %~ sk of
    Proved Refl -> case GHC.TypeNats.sameNat (Proxy @src) (Proxy @m) of
      Just Refl -> blk
      Nothing -> error "findBC: source dim mismatch (unreachable by Schur)"
    Disproved _ -> findBC sj rest

composeGo ::
  forall g a b c.
  (RepLookup g) =>
  SRep g a ->
  SRep g b ->
  SRep g c ->
  IntertwinerSectors g (IntertwinerHom g a b) ->
  [BCEntry g c] ->
  IntertwinerSectors g (IntertwinerHom g a c)
composeGo SRepNilU1 _ _ InterNil _ = InterNil
composeGo SRepNilSU2 _ _ InterNil _ = InterNil
composeGo (SRepCons @az @an saz rest) sb sc ab bcIx =
  case (sLookupMult @U1 saz sb, sLookupMult @U1 saz sc) of
    (Absent, Absent) ->
      composeGo rest sb sc ab bcIx
    (Absent, Present (_ :: Proxy p)) ->
      InterCons (zeroBlock @p @an) (composeGo rest sb sc ab bcIx)
    (Present (_ :: Proxy m), Absent) ->
      case ab of
        InterCons _ abRest -> composeGo rest sb sc abRest bcIx
    (Present (_ :: Proxy m), Present (_ :: Proxy p)) ->
      case ab of
        InterCons abBlk abRest ->
          InterCons
            (composeBlock (findBC saz bcIx) abBlk)
            (composeGo rest sb sc abRest bcIx)
composeGo (SRepConsSU2 @aj @an saj rest) sb sc ab bcIx =
  case (sLookupMult @SU2 saj sb, sLookupMult @SU2 saj sc) of
    (Absent, Absent) ->
      composeGo rest sb sc ab bcIx
    (Absent, Present (_ :: Proxy p)) ->
      InterCons (zeroBlock @p @an) (composeGo rest sb sc ab bcIx)
    (Present (_ :: Proxy m), Absent) ->
      case ab of
        InterCons _ abRest -> composeGo rest sb sc abRest bcIx
    (Present (_ :: Proxy m), Present (_ :: Proxy p)) ->
      case ab of
        InterCons abBlk abRest ->
          InterCons
            (composeBlock (findBC saj bcIx) abBlk)
            (composeGo rest sb sc abRest bcIx)

--------------------------------------------------------------------------------
-- Vector space on Schur-block spines (blockwise @+@ / scale)
--------------------------------------------------------------------------------

zeroInterSectors ::
  (BuildIdHom g hom) => IntertwinerSectors g hom
zeroInterSectors = scaleInterSectors 0 idHom

addInterSectors ::
  IntertwinerSectors g hom ->
  IntertwinerSectors g hom ->
  IntertwinerSectors g hom
addInterSectors InterNil InterNil = InterNil
addInterSectors (InterCons a as) (InterCons b bs) =
  InterCons (addBlock a b) (addInterSectors as bs)

scaleInterSectors ::
  Complex Double ->
  IntertwinerSectors g hom ->
  IntertwinerSectors g hom
scaleInterSectors _ InterNil = InterNil
scaleInterSectors μ (InterCons a as) =
  InterCons (scaleBlock μ a) (scaleInterSectors μ as)

negateInterSectors ::
  IntertwinerSectors g hom -> IntertwinerSectors g hom
negateInterSectors InterNil = InterNil
negateInterSectors (InterCons a as) =
  InterCons (negateBlock a) (negateInterSectors as)

instance
  (BuildIdHom g (IntertwinerHom g r q)) =>
  AdditiveGroup (Intertwiner g r q)
  where
  zeroV = MkIntertwiner zeroInterSectors
  MkIntertwiner a ^+^ MkIntertwiner b = MkIntertwiner (addInterSectors a b)
  MkIntertwiner a ^-^ MkIntertwiner b = MkIntertwiner (addInterSectors a (negateInterSectors b))
  negateV (MkIntertwiner s) = MkIntertwiner (negateInterSectors s)

instance
  (BuildIdHom g (IntertwinerHom g r q)) =>
  VectorSpace (Intertwiner g r q)
  where
  type Scalar (Intertwiner g r q) = Complex Double
  μ *^ MkIntertwiner s = MkIntertwiner (scaleInterSectors μ s)

compose ::
  forall g a b c.
  ( RepLookup g,
    KnownRep g a,
    KnownRep g b,
    KnownRep g c
  ) =>
  Intertwiner g b c -> Intertwiner g a b -> Intertwiner g a c
compose (MkIntertwiner bc) (MkIntertwiner ab) =
  MkIntertwiner
    ( composeGo
        (repSing @g @a)
        (repSing @g @b)
        (repSing @g @c)
        ab
        (bcIndex (repSing @g @b) (repSing @g @c) bc)
    )

instance Category (Intertwiner U1) where
  type
    Object (Intertwiner U1) a =
      ( RepLookup U1,
        KnownRep U1 a,
        KnownNat (RepDim U1 a),
        BuildIdHom U1 (IntertwinerHom U1 a a)
      )
  id = mkIdHom @U1
  (.) = compose @U1

instance Category (Intertwiner SU2) where
  type
    Object (Intertwiner SU2) a =
      ( RepLookup SU2,
        KnownRep SU2 a,
        KnownNat (RepDim SU2 a),
        BuildIdHom SU2 (IntertwinerHom SU2 a a)
      )
  id = mkIdHom @SU2
  (.) = compose @SU2

--------------------------------------------------------------------------------
-- Sector layout: prefix offsets in flat @C (RepDim g r)@ storage
--------------------------------------------------------------------------------

natValInt :: (KnownNat n) => Proxy n -> Int
natValInt = fromIntegral . natVal

targetIrrepOffset ::
  forall g (j :: Irreps g) (q :: Rep g).
  (KnownRep g q) =>
  Sing j -> SRep g q -> Int
targetIrrepOffset sj = go 0
  where
    go :: forall q0. Int -> SRep g q0 -> Int
    go _ SRepNilU1 =
      error "targetIrrepOffset: irrep absent (unreachable for hom blocks)"
    go _ SRepNilSU2 =
      error "targetIrrepOffset: irrep absent (unreachable for hom blocks)"
    go !off (SRepCons @j2 @m sz2 rest) =
      let stride = natValInt (Proxy @(SectorDim U1 j2 m))
       in case sIrrepEq @U1 sj sz2 of
            IrrepEqTrue -> off
            IrrepEqFalse -> go (off + stride) rest
    go !off (SRepConsSU2 @j2 @m sj2 rest) =
      let stride = natValInt (Proxy @(SectorDim SU2 j2 m))
       in case sIrrepEq @SU2 sj sj2 of
            IrrepEqTrue -> off
            IrrepEqFalse -> go (off + stride) rest

takeAtOffset :: forall n total. (KnownNat n, KnownNat total) => Int -> C total -> C n
takeAtOffset off v =
  fromMaybe (error "takeAtOffset: slice out of range") $
    create (V.fromList (P.take (natValInt (Proxy @n)) (P.drop off (V.toList (extract v)))))

writeAtOffset :: forall m total. (KnownNat m, KnownNat total) => Int -> C m -> C total -> C total
writeAtOffset off block vec =
  fromMaybe (error "writeAtOffset: patch out of range") $
    create (V.fromList merged)
  where
    xs = V.toList (extract vec)
    ys = V.toList (extract block)
    m = natValInt (Proxy @m)
    merged = P.take off xs P.++ ys P.++ P.drop (off + m) xs

data CompiledStep where
  CompiledStep ::
    forall sm sn.
    (KnownNat sm, KnownNat sn) =>
    !Int -> !Int -> !(M sm sn) -> CompiledStep

runCompiledStep ::
  forall rdim qdim.
  (KnownNat rdim, KnownNat qdim) =>
  CompiledStep -> C rdim -> C qdim -> C qdim
runCompiledStep (CompiledStep @sm @sn srcOff tgtOff mat) input = writeAtOffset @sm tgtOff (app mat (takeAtOffset @sn srcOff input))

collectCompiledSteps ::
  forall g r q hom.
  (RepLookup g, KnownRep g q, ExpandBlock g) =>
  SRep g r -> SRep g q -> IntertwinerSectors g hom -> Int -> [CompiledStep]
collectCompiledSteps SRepNilU1 _ InterNil _ = []
collectCompiledSteps SRepNilU1 _ (InterCons _ _) _ =
  error "collectCompiledSteps: hom spine longer than source rep (unreachable)"
collectCompiledSteps SRepNilSU2 _ InterNil _ = []
collectCompiledSteps SRepNilSU2 _ (InterCons _ _) _ =
  error "collectCompiledSteps: hom spine longer than source rep (unreachable)"
collectCompiledSteps (SRepCons @z @m saz srest) sq hom !off =
  let srcDim = natValInt (Proxy @(SectorDim U1 z m))
   in case sLookupMult @U1 saz sq of
        Absent -> collectCompiledSteps srest sq hom (off + srcDim)
        Present (_ :: Proxy srcMult) -> case hom of
          InterCons blk homRest ->
            CompiledStep off (targetIrrepOffset @U1 @z saz sq) (expandBlock @U1 (Proxy @z) blk)
              : collectCompiledSteps srest sq homRest (off + srcDim)
          InterNil ->
            error "collectCompiledSteps: hom spine exhausted early (unreachable)"
collectCompiledSteps (SRepConsSU2 @j @m saj srest) sq hom !off =
  let srcDim = natValInt (Proxy @(SectorDim SU2 j m))
   in case sLookupMult @SU2 saj sq of
        Absent -> collectCompiledSteps srest sq hom (off + srcDim)
        Present (_ :: Proxy srcMult) -> case hom of
          InterCons blk homRest ->
            CompiledStep off (targetIrrepOffset @SU2 @j saj sq) (expandBlock @SU2 (Proxy @j) blk)
              : collectCompiledSteps srest sq homRest (off + srcDim)
          InterNil ->
            error "collectCompiledSteps: hom spine exhausted early (unreachable)"

type HasIntertwiner g r q =
  ( RepLookup g,
    ExpandBlock g,
    KnownRep g r,
    KnownNat (RepDim g r),
    KnownRep g q,
    KnownNat (RepDim g q)
  )

-- | Forget an intertwiner to a linear map on flat @C (RepDim g r)@ storage.
intertwinerLinear ::
  forall g r q.
  (HasIntertwiner g r q) =>
  Intertwiner g r q ->
  C (RepDim g r) -+> C (RepDim g q)
intertwinerLinear (MkIntertwiner sectors) =
  linearFunction (\input -> foldl (\acc step -> runCompiledStep step input acc) (konst 0) steps)
  where
    steps = collectCompiledSteps (repSing @g @r) (repSing @g @q) sectors 0
