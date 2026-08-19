{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Group-indexed forgetful category of representation morphisms.
--
-- Objects are nested @RepObj g@ (@'I@, @'REP@ spines, @':⊗:@ products).
-- Morphisms include leaf @Fuse@, structural isomorphisms (@Assoc@, @Swap@,
-- unitors), fused associators @FMove@\/@FMoveInv@ and braidings
-- @RMove@\/@RMoveInv@ (indexed by nested @Tensor@), monoidal product @OTimes@,
-- intertwiners on reduced spines, and free @MorId@ \/ @Comp@.
--
-- Important: composing @Mor@ values does __not__ densify. Only @fmap'@ forgets
-- to maps on @ToVector@. Unfused @Assoc@\/@Swap@\/unitors are cheap Vec
-- coercions; @Fuse@ is CG. @FMove@ is the fused monoidal associator between
-- @'REP (Tensor (Tensor r q) s)@ and @'REP (Tensor r (Tensor q s))@ — defined
-- via F-symbols \/ 6j as an @Intertwiner@, __not__ by conjugating @Fuse@ with
-- Vec @Assoc@. @RMove@ is the fused braiding
-- @'REP (Tensor r q) → 'REP (Tensor q r)@ (@Fuse ∘ Swap ∘ Fuse†@), not Vec
-- @Swap@ alone.
--
-- Forgetting @Fuse@ is group-specific ('ForgetFuse'): U(1) Kronecker flatten;
-- SU(2) Clebsch–Gordan. Associators → @lassocTensor@\/@rassocTensor@; braiding
-- → @transposeTensor@; unitors → flat-tensor + @C 1@ scalarization; @OTimes@ →
-- @tensorOfMaps@; @FMove@\/@RMove@ carry @Intertwiner@ from
-- 'Representations.CG.FSymbol' \/ 'Representations.CG.RSymbol'.
module Representations.Mor
  ( Mor (..),
    GObj,
    ForgetFuse (..),
    fmap',
    fmapSectors,
    fMoveU1,
    fMoveU1Inv,
    fMoveSU2,
    fMoveSU2Inv,
    rMoveU1,
    rMoveU1Inv,
    rMoveSU2,
    rMoveSU2Inv,
    type (-&>),
    CanFuse,
    CanFMove,
    CanRMove,
    GTensor,
    GLinear,
  )
where

import Control.Arrow.Constrained (arr, ($))
import Control.Category.Constrained (Category (..))
import Data.Complex (Complex)
import Data.Proxy (Proxy (..))
import Data.VectorSpace (VectorSpace, (*^))
import GHC.TypeLits (KnownNat, type (*))
import Math.LinearMap.Asserted (linearFunction, type (-+>))
import Math.LinearMap.Category
  ( LSpace,
    LinearSpace (..),
    Scalar,
    TensorSpace (..),
    applyDualVector,
    fmapTensor,
    fromFlatTensor,
    toFlatTensor,
    transposeTensor,
    (-+$>),
  )
import Math.LinearMap.Category.Backend.HMatrix ()
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Coercion (lassocTensor, rassocTensor, (-+$=>))
import Math.VectorSpace.DimensionAware (toArray, unsafeFromArray)
import Numeric.LinearAlgebra.Static (C, konst)
import Numeric.LinearAlgebra.Static.COrphans ()
import Representations.CG.FSymbol
  ( PackSchur,
    fSymbolHomSU2,
    fSymbolHomSU2Inv,
    fSymbolHomU1,
    fSymbolHomU1Inv,
  )
import Representations.CG.RSymbol
  ( rSymbolHomSU2,
    rSymbolHomSU2Inv,
    rSymbolHomU1,
    rSymbolHomU1Inv,
  )
import Representations.CG.SU2 (fuseSU2Flat)
import Representations.CG.U1 (fuseU1Flat)
import Representations.Group (Group (..), IntertwinerHom, RepDim)
import Representations.Intertwiner
  ( BuildIdHom,
    HasIntertwiner,
    Intertwiner (..),
    compose,
    intertwinerLinear,
  )
import Representations.Rep.Obj (RepObj (..), ToSectors, ToVector)
import Representations.Rep.Sectors (ApplyHom, intertwinerEndoSectors, (⊗^))
import Representations.Rep.Singleton (KnownRep (..))
import Representations.Rep.Tensor (Tensor)
import Prelude hiding (Functor (..), id, ($), (.))

type ℂ = Complex Double

-- | Reduced-spine fusion: @RepDim (r ⊗ q) ~ RepDim r * RepDim q@.
type CanFuse g r q =
  ( KnownRep g r,
    KnownRep g q,
    KnownNat (RepDim g r),
    KnownNat (RepDim g q),
    KnownNat (RepDim g r * RepDim g q),
    KnownNat (RepDim g (Tensor g r q)),
    RepDim g (Tensor g r q) ~ (RepDim g r * RepDim g q)
  )

-- | Fused associator @(r ⊗ q) ⊗ s ⇄ r ⊗ (q ⊗ s)@ on reduced spines.
type CanFMove g r q s =
  ( KnownRep g r,
    KnownRep g q,
    KnownRep g s,
    HasIntertwiner
      g
      (Tensor g (Tensor g r q) s)
      (Tensor g r (Tensor g q s))
  )

-- | Fused braiding @r ⊗ q ⇄ q ⊗ r@ on reduced spines.
type CanRMove g r q =
  ( KnownRep g r,
    KnownRep g q,
    HasIntertwiner g (Tensor g r q) (Tensor g q r)
  )

-- | @ToVector g a@ is a complex tensor space (unfused associators).
type GTensor g a =
  ( TensorSpace (ToVector g a),
    Scalar (ToVector g a) ~ ℂ
  )

-- | @ToVector g a@ is a complex linear space (braiding, unitors).
type GLinear g a =
  ( LinearSpace (ToVector g a),
    Scalar (ToVector g a) ~ ℂ
  )

-- | Morphisms in the forgetful rep category for group @g@.
data Mor (g :: Group) (a :: RepObj g) (b :: RepObj g) where
  RepInter ::
    (HasIntertwiner g r q) =>
    Intertwiner g r q ->
    Mor g ('REP r) ('REP q)
  -- | Fuse two reduced spines (leaf tensor only).
  Fuse ::
    forall g r q.
    (CanFuse g r q) =>
    Mor g ('REP r ':⊗: 'REP q) ('REP (Tensor g r q))
  -- | Fused associator (F-move):
  -- @α : (r ⊗ q) ⊗ s → r ⊗ (q ⊗ s)@ on reduced spines.
  -- Parenthesization of @Tensor@ is the fusion-tree proof.
  -- Proxies are required because @Tensor@ is non-injective.
  -- Build with 'fMoveSU2' \/ 'fMoveU1' (packs F-symbols into the intertwiner).
  FMove ::
    (CanFMove g r q s) =>
    Intertwiner
      g
      (Tensor g (Tensor g r q) s)
      (Tensor g r (Tensor g q s)) ->
    Proxy r ->
    Proxy q ->
    Proxy s ->
    Mor
      g
      ('REP (Tensor g (Tensor g r q) s))
      ('REP (Tensor g r (Tensor g q s)))
  -- | Inverse F-move: @α⁻¹ : r ⊗ (q ⊗ s) → (r ⊗ q) ⊗ s@.
  FMoveInv ::
    (CanFMove g r q s) =>
    Intertwiner
      g
      (Tensor g r (Tensor g q s))
      (Tensor g (Tensor g r q) s) ->
    Proxy r ->
    Proxy q ->
    Proxy s ->
    Mor
      g
      ('REP (Tensor g r (Tensor g q s)))
      ('REP (Tensor g (Tensor g r q) s))
  -- | Fused braiding (R-move): @σ : r ⊗ q → q ⊗ r@ on reduced spines.
  -- Build with 'rMoveSU2' \/ 'rMoveU1'.
  RMove ::
    (CanRMove g r q) =>
    Intertwiner g (Tensor g r q) (Tensor g q r) ->
    Proxy r ->
    Proxy q ->
    Mor g ('REP (Tensor g r q)) ('REP (Tensor g q r))
  -- | Inverse R-move: @σ⁻¹ : q ⊗ r → r ⊗ q@.
  RMoveInv ::
    (CanRMove g r q) =>
    Intertwiner g (Tensor g q r) (Tensor g r q) ->
    Proxy r ->
    Proxy q ->
    Mor g ('REP (Tensor g q r)) ('REP (Tensor g r q))
  -- | Associator @α : a ⊗ (b ⊗ c) → (a ⊗ b) ⊗ c@ (unfused Vec associator).
  Assoc ::
    forall g x y z.
    (GTensor g x, GTensor g y, GTensor g z) =>
    Mor g (x ':⊗: (y ':⊗: z)) ((x ':⊗: y) ':⊗: z)
  -- | Inverse associator @α⁻¹ : (a ⊗ b) ⊗ c → a ⊗ (b ⊗ c)@.
  AssocInv ::
    forall g x y z.
    (GTensor g x, GTensor g y, GTensor g z) =>
    Mor g ((x ':⊗: y) ':⊗: z) (x ':⊗: (y ':⊗: z))
  -- | Braiding @σ : a ⊗ b → b ⊗ a@.
  Swap ::
    forall g x y.
    (GLinear g x, GLinear g y) =>
    Mor g (x ':⊗: y) (y ':⊗: x)
  -- | Left unitor @λ : I ⊗ a → a@.
  LUnit ::
    forall g x.
    (GLinear g x) =>
    Mor g ('I ':⊗: x) x
  -- | Inverse left unitor @λ⁻¹ : a → I ⊗ a@.
  LUnitInv ::
    forall g x.
    (GLinear g x) =>
    Mor g x ('I ':⊗: x)
  -- | Right unitor @ρ : a ⊗ I → a@.
  RUnit ::
    forall g x.
    (GLinear g x) =>
    Mor g (x ':⊗: 'I) x
  -- | Inverse right unitor @ρ⁻¹ : a → a ⊗ I@.
  RUnitInv ::
    forall g x.
    (GLinear g x) =>
    Mor g x (x ':⊗: 'I)
  -- | Monoidal product of morphisms @f ⊗ g : a⊗c → b⊗d@.
  -- Stays symbolic until @fmap'@ (then @tensorOfMaps@).
  OTimes ::
    ( GObj g a,
      GObj g b,
      GObj g c,
      GObj g d,
      LSpace (ToVector g a),
      LSpace (ToVector g b),
      LSpace (ToVector g c),
      LSpace (ToVector g d)
    ) =>
    Mor g a b ->
    Mor g c d ->
    Mor g (a ':⊗: c) (b ':⊗: d)
  MorId :: Mor g a a
  Comp :: (GObj g b) => Mor g b c -> Mor g a b -> Mor g a c

-- | Infix for @Mor g@. @g@ is recovered from the objects because 'Rep' (and
-- 'Irreps') are injective: @[(Z, Nat)]@ is U(1), @[(Nat, Nat)]@ is SU(2).
-- Ambiguous only when both sides are group-polymorphic, e.g. @'I -&> 'I@.
infixr 1 -&>

type (a :: RepObj g) -&> (b :: RepObj g) = Mor g a b

-- | Category objects of @Mor g@: complex tensor space on @ToVector@.
class (GTensor g a) => GObj (g :: Group) (a :: RepObj g)

instance GObj g 'I

instance
  ( KnownRep g r,
    KnownNat (RepDim g r),
    BuildIdHom g (IntertwinerHom g r r)
  ) =>
  GObj g ('REP r)

instance (GObj g a, GObj g b) => GObj g (a ':⊗: b)

-- | Group-specific forgetful image of leaf @Fuse@.
class ForgetFuse (g :: Group) where
  forgetFuse ::
    forall r q.
    (CanFuse g r q) =>
    Proxy r ->
    Proxy q ->
    ToVector g ('REP r ':⊗: 'REP q) -+> ToVector g ('REP (Tensor g r q))

instance ForgetFuse U1 where
  forgetFuse (_ :: Proxy r) (_ :: Proxy q) =
    linearFunction $ \t ->
      unsafeFromArray (fuseU1Flat (repSing @U1 @r) (repSing @U1 @q) (toArray t))

instance ForgetFuse SU2 where
  forgetFuse (_ :: Proxy r) (_ :: Proxy q) =
    linearFunction $ \t ->
      unsafeFromArray (fuseSU2Flat (repSing @SU2 @r) (repSing @SU2 @q) (toArray t))

-- | U(1) F-move: identity on coalesced @Tensor@ spines.
fMoveU1 ::
  forall r q s.
  ( CanFMove U1 r q s,
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
  'REP (Tensor U1 (Tensor U1 r q) s)
    -&> 'REP (Tensor U1 r (Tensor U1 q s))
fMoveU1 pr pq ps = FMove (fSymbolHomU1 pr pq ps) pr pq ps

fMoveU1Inv ::
  forall r q s.
  ( CanFMove U1 r q s,
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
  'REP (Tensor U1 r (Tensor U1 q s))
    -&> 'REP (Tensor U1 (Tensor U1 r q) s)
fMoveU1Inv pr pq ps = FMoveInv (fSymbolHomU1Inv pr pq ps) pr pq ps

-- | SU(2) F-move from CG-coherent Schur blocks ('Representations.CG.FSymbol').
fMoveSU2 ::
  forall r q s.
  ( CanFMove SU2 r q s,
    KnownRep SU2 (Tensor SU2 r q),
    KnownRep SU2 (Tensor SU2 q s),
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
  'REP (Tensor SU2 (Tensor SU2 r q) s)
    -&> 'REP (Tensor SU2 r (Tensor SU2 q s))
fMoveSU2 pr pq ps = FMove (fSymbolHomSU2 pr pq ps) pr pq ps

fMoveSU2Inv ::
  forall r q s.
  ( CanFMove SU2 r q s,
    KnownRep SU2 (Tensor SU2 r q),
    KnownRep SU2 (Tensor SU2 q s),
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
  'REP (Tensor SU2 r (Tensor SU2 q s))
    -&> 'REP (Tensor SU2 (Tensor SU2 r q) s)
fMoveSU2Inv pr pq ps = FMoveInv (fSymbolHomSU2Inv pr pq ps) pr pq ps

-- | U(1) R-move: identity on coalesced @Tensor@ spines.
rMoveU1 ::
  forall r q.
  ( CanRMove U1 r q,
    BuildIdHom
      U1
      (IntertwinerHom U1 (Tensor U1 r q) (Tensor U1 q r))
  ) =>
  Proxy r ->
  Proxy q ->
  'REP (Tensor U1 r q) -&> 'REP (Tensor U1 q r)
rMoveU1 pr pq = RMove (rSymbolHomU1 pr pq) pr pq

rMoveU1Inv ::
  forall r q.
  ( CanRMove U1 r q,
    BuildIdHom
      U1
      (IntertwinerHom U1 (Tensor U1 q r) (Tensor U1 r q))
  ) =>
  Proxy r ->
  Proxy q ->
  'REP (Tensor U1 q r) -&> 'REP (Tensor U1 r q)
rMoveU1Inv pr pq = RMoveInv (rSymbolHomU1Inv pr pq) pr pq

-- | SU(2) R-move from CG-coherent Schur blocks ('Representations.CG.RSymbol').
rMoveSU2 ::
  forall r q.
  ( CanRMove SU2 r q,
    PackSchur
      (IntertwinerHom SU2 (Tensor SU2 r q) (Tensor SU2 q r))
  ) =>
  Proxy r ->
  Proxy q ->
  'REP (Tensor SU2 r q) -&> 'REP (Tensor SU2 q r)
rMoveSU2 pr pq = RMove (rSymbolHomSU2 pr pq) pr pq

rMoveSU2Inv ::
  forall r q.
  ( CanRMove SU2 r q,
    PackSchur
      (IntertwinerHom SU2 (Tensor SU2 q r) (Tensor SU2 r q))
  ) =>
  Proxy r ->
  Proxy q ->
  'REP (Tensor SU2 q r) -&> 'REP (Tensor SU2 r q)
rMoveSU2Inv pr pq = RMoveInv (rSymbolHomSU2Inv pr pq) pr pq

--------------------------------------------------------------------------------
-- Forgetful image
--------------------------------------------------------------------------------

oneC1 :: C 1
oneC1 = konst 1

scalarizeC1 :: C 1 -+> ℂ
scalarizeC1 = applyDualVector -+$> oneC1

embedC1 :: ℂ -+> C 1
embedC1 = linearFunction (*^ oneC1)

-- | Forget a @Mor g@ to a map on @ToVector g@ spaces.
fmap' ::
  forall g a b.
  ( Object (Mor g) a,
    Object (Mor g) b,
    ForgetFuse g
  ) =>
  Mor g a b ->
  ToVector g a -+> ToVector g b
fmap' (RepInter mor) = intertwinerLinear @g mor
fmap' (Fuse @_ @r @q) = forgetFuse @g (Proxy @r) (Proxy @q)
fmap' (FMove mor _ _ _) = intertwinerLinear @g mor
fmap' (FMoveInv mor _ _ _) = intertwinerLinear @g mor
fmap' (RMove mor _ _) = intertwinerLinear @g mor
fmap' (RMoveInv mor _ _) = intertwinerLinear @g mor
fmap' (Assoc @_ @x @y @z) =
  linearFunction
    (lassocTensor @ℂ @(ToVector g x) @(ToVector g y) @(ToVector g z) -+$=>)
fmap' (AssocInv @_ @x @y @z) =
  linearFunction
    (rassocTensor @ℂ @(ToVector g x) @(ToVector g y) @(ToVector g z) -+$=>)
fmap' (Swap @_ @x @y) =
  transposeTensor @(ToVector g x) @(ToVector g y)
fmap' (LUnit @_ @x) =
  fromFlatTensor @(ToVector g x)
    . (fmapTensor @(ToVector g x) -+$> scalarizeC1)
    . transposeTensor @(C 1) @(ToVector g x)
fmap' (LUnitInv @_ @x) =
  transposeTensor @(ToVector g x) @(C 1)
    . (fmapTensor @(ToVector g x) -+$> embedC1)
    . toFlatTensor @(ToVector g x)
fmap' (RUnit @_ @x) =
  fromFlatTensor @(ToVector g x)
    . (fmapTensor @(ToVector g x) -+$> scalarizeC1)
fmap' (RUnitInv @_ @x) =
  (fmapTensor @(ToVector g x) -+$> embedC1)
    . toFlatTensor @(ToVector g x)
fmap' (OTimes f h) =
  linearFunction ((arr (fmap' f) ⊗^ arr (fmap' h)) $)
fmap' MorId = id
fmap' (Comp h f) = fmap' h . fmap' f

-- | Forget a reduced-spine endomorphism, applying @coeff ⊗ id@ per sector.
-- General @r → q@ (and @Fuse@ / unfused structural maps) are unfinished.
fmapSectors ::
  forall g r.
  ( ApplyHom g (IntertwinerHom g r r) r,
    VectorSpace (ToSectors g ('REP r)),
    Scalar (ToSectors g ('REP r)) ~ ℂ
  ) =>
  Mor g ('REP r) ('REP r) ->
  ToSectors g ('REP r) -+> ToSectors g ('REP r)
fmapSectors (RepInter mor) = intertwinerEndoSectors @g mor
fmapSectors (FMove mor _ _ _) = intertwinerEndoSectors @g mor
fmapSectors (FMoveInv mor _ _ _) = intertwinerEndoSectors @g mor
fmapSectors (RMove mor _ _) = intertwinerEndoSectors @g mor
fmapSectors (RMoveInv mor _ _) = intertwinerEndoSectors @g mor
fmapSectors MorId = linearFunction (\x -> x)
fmapSectors (Comp _ _) =
  error "fmapSectors: composition is only defined on a single reduced spine"

instance Category (Mor g) where
  type Object (Mor g) a = GObj g a

  id :: forall a. (Object (Mor g) a) => Mor g a a
  id = MorId

  MorId . f = f
  h . MorId = h
  RepInter k . RepInter f = RepInter (compose @g k f)
  h . f = Comp h f
