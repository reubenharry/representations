{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Pretty-printing for Schur-block intertwiners.
--
-- Shows both the coefficient (Schur) blocks labeled by irrep and the expanded
-- dense matrix in sector-block form (@M_{m,n}(ℂ) ⊗ I_{dim j}@ for SU(2)).
module Representations.Intertwiner.Pretty
  ( PrettyInter (..),
    ppr,
    pprDense,
  )
where

import Data.Complex (Complex (..))
import Data.List (intercalate)
import Data.Proxy (Proxy (..))
import Data.Singletons (Sing, fromSing)
import GHC.TypeLits (KnownNat, natVal)
import qualified Numeric.LinearAlgebra as LA
import Numeric.LinearAlgebra.Static (unwrap)
import Representations.Group
  ( Group (..),
    IrrepDim,
    Irreps,
    Rep,
    RepDim,
    SectorDim,
  )
import Representations.Intertwiner
  ( Intertwiner (..),
    IntertwinerSectors (..),
    LookupResult (..),
    RepLookup (..),
    targetIrrepOffset,
  )
import Representations.Rep.HomBlock (ExpandBlock (..))
import Representations.Rep.Singleton (KnownRep (..), SRep (..))
import Representations.Utils (Z (..))
import Text.Printf (printf)

-- | REPL helpers.
ppr :: (PrettyInter g r q) => Intertwiner g r q -> IO ()
ppr = putStrLn . prettyIntertwiner

pprDense :: (PrettyInter g r q) => Intertwiner g r q -> IO ()
pprDense = putStrLn . prettyIntertwinerDense

class PrettyInter (g :: Group) (r :: Rep g) (q :: Rep g) where
  -- | Schur blocks + sector layout.
  prettyIntertwiner :: Intertwiner g r q -> String

  -- | Expanded dense forgetful matrix (block-diagonal).
  prettyIntertwinerDense :: Intertwiner g r q -> String

class PrettyLabel (g :: Group) where
  prettyIrrep :: Sing (j :: Irreps g) -> String
  prettyGroup :: String
  schurSubtitle :: String

instance PrettyLabel U1 where
  prettyIrrep sz = prettyZU1 (fromSing sz)
  prettyGroup = "U(1)"
  schurSubtitle = "Schur blocks (charge → multiplicity matrix):"

instance PrettyLabel SU2 where
  prettyIrrep sj = prettySU2 (fromSing sj)
  prettyGroup = "SU(2)"
  schurSubtitle = "Schur blocks (j → multiplicity matrix; expands as ⊗ I_{2j+1}):"

instance
  ( PrettyLabel g,
    KnownRep g r,
    KnownRep g q,
    KnownNat (RepDim g r),
    KnownNat (RepDim g q),
    RepLookup g,
    ExpandBlock g
  ) =>
  PrettyInter g r q
  where
  prettyIntertwiner (MkIntertwiner hom) =
    prettyGo
      (repSing @g @r)
      (repSing @g @q)
      hom
      (fromIntegral (natVal (Proxy @(RepDim g r))))
      (fromIntegral (natVal (Proxy @(RepDim g q))))
  prettyIntertwinerDense (MkIntertwiner hom) =
    renderDenseMatrix
      (fromIntegral (natVal (Proxy @(RepDim g q))))
      (fromIntegral (natVal (Proxy @(RepDim g r))))
      (denseBlocks (repSing @g @r) (repSing @g @q) hom 0)

--------------------------------------------------------------------------------
-- Labels / formatting
--------------------------------------------------------------------------------

prettyZU1 :: Z -> String
prettyZU1 Zero = "0"
prettyZU1 (Pos n) = '+' : show n
prettyZU1 (Neg n) = '-' : show n

prettySU2 :: (Integral a) => a -> String
prettySU2 tj
  | even tj' = show (tj' `div` 2)
  | otherwise = show tj' ++ "/2"
  where
    tj' = toInteger tj

prettyC :: Complex Double -> String
prettyC (a :+ b)
  | abs b < 1e-12 && abs a < 1e-12 = "0"
  | abs b < 1e-12 = printf "%.2g" a
  | abs a < 1e-12 = printf "%.2gj" b
  | b >= 0 = printf "%.2g+%.2gj" a b
  | otherwise = printf "%.2g%.2gj" a b

prettyMat :: LA.Matrix (Complex Double) -> String
prettyMat mat =
  let cells = map (map prettyC) (LA.toLists mat)
      widths = foldr (zipWith max . map length) (repeat 0) cells
      padL w s = replicate (w - length s) ' ' ++ s
      fmt row = intercalate "  " (zipWith padL widths row)
   in intercalate "\n" (map (("    " ++) . fmt) cells)

--------------------------------------------------------------------------------
-- Schur-block views
--------------------------------------------------------------------------------

prettyGo ::
  forall g r q hom.
  (PrettyLabel g, RepLookup g) =>
  SRep g r ->
  SRep g q ->
  IntertwinerSectors g hom ->
  Int ->
  Int ->
  String
prettyGo sr sq hom dimR dimQ =
  unlines $
    [ "Intertwiner " ++ prettyGroup @g ++ "  dim " ++ show dimR ++ " → " ++ show dimQ,
      schurSubtitle @g
    ]
      ++ emptyOrNone (schurBlocks @g sr sq hom 0)
      ++ [""]
      ++ sectorLines @g "domain" sr
      ++ sectorLines @g "codomain" sq

emptyOrNone :: [String] -> [String]
emptyOrNone [] = ["  (none)"]
emptyOrNone xs = xs

schurBlocks ::
  forall g r q hom.
  (PrettyLabel g, RepLookup g) =>
  SRep g r -> SRep g q -> IntertwinerSectors g hom -> Int -> [String]
schurBlocks SRepNilU1 _ _ _ = []
schurBlocks SRepNilSU2 _ _ _ = []
schurBlocks (SRepCons @j @m saj rest) sq hom off =
  schurStep @U1 @j @m saj rest sq hom off
schurBlocks (SRepConsSU2 @j @m saj rest) sq hom off =
  schurStep @SU2 @j @m saj rest sq hom off

schurStep ::
  forall g j m r' q hom.
  ( PrettyLabel g,
    RepLookup g,
    KnownNat m,
    KnownNat (SectorDim g j m),
    KnownNat (IrrepDim g j)
  ) =>
  Sing j ->
  SRep g r' ->
  SRep g q ->
  IntertwinerSectors g hom ->
  Int ->
  [String]
schurStep saj rest sq hom off =
  let stride :: Int
      stride = fromIntegral (natVal (Proxy @(SectorDim g j m)))
   in case (sLookupMult @g saj sq, hom) of
        (Absent, _) -> schurBlocks rest sq hom (off + stride)
        (Present {}, InterNil) -> ["  <hom spine exhausted>"]
        (Present (_ :: Proxy n), InterCons blk homRest) ->
          let mat = unwrap blk
              mI = fromIntegral (natVal (Proxy @m)) :: Int
              nI = fromIntegral (natVal (Proxy @n)) :: Int
              irrepD = fromIntegral (natVal (Proxy @(IrrepDim g j))) :: Int
              hdr =
                printf
                  "  %s  mult %d→%d  expands %d×%d  @col %d:"
                  (prettyIrrep @g saj)
                  mI
                  nI
                  (mI * irrepD)
                  (nI * irrepD)
                  off
           in (hdr : lines (prettyMat mat))
                ++ schurBlocks rest sq homRest (off + stride)

sectorLines :: forall g r. (PrettyLabel g) => String -> SRep g r -> [String]
sectorLines tag SRepNilU1 = ["  " ++ tag ++ " sectors: (empty)"]
sectorLines tag SRepNilSU2 = ["  " ++ tag ++ " sectors: (empty)"]
sectorLines tag s = ("  " ++ tag ++ " sectors:") : sectorGo s 0

sectorGo :: forall g r'. (PrettyLabel g) => SRep g r' -> Int -> [String]
sectorGo SRepNilU1 _ = []
sectorGo SRepNilSU2 _ = []
sectorGo (SRepCons @j @m saj rest) !off =
  sectorLine @U1 @j @m saj rest off
sectorGo (SRepConsSU2 @j @m saj rest) !off =
  sectorLine @SU2 @j @m saj rest off

sectorLine ::
  forall g j m r'.
  (PrettyLabel g, KnownNat m, KnownNat (SectorDim g j m)) =>
  Sing j -> SRep g r' -> Int -> [String]
sectorLine saj rest off =
  let stride :: Int
      stride = fromIntegral (natVal (Proxy @(SectorDim g j m)))
      line =
        printf
          "    %s ×%d  [%d..%d)"
          (prettyIrrep @g saj)
          (fromIntegral (natVal (Proxy @m)) :: Int)
          off
          (off + stride)
   in line : sectorGo rest (off + stride)

--------------------------------------------------------------------------------
-- Dense expanded matrix
--------------------------------------------------------------------------------

type BlockStamp = (Int, Int, LA.Matrix (Complex Double))

denseBlocks ::
  forall g r q hom.
  (PrettyLabel g, RepLookup g, ExpandBlock g, KnownRep g q) =>
  SRep g r -> SRep g q -> IntertwinerSectors g hom -> Int -> [BlockStamp]
denseBlocks SRepNilU1 _ _ _ = []
denseBlocks SRepNilSU2 _ _ _ = []
denseBlocks (SRepCons @j @m saj rest) sq hom off =
  let stride :: Int
      stride = fromIntegral (natVal (Proxy @(SectorDim U1 j m)))
   in case (sLookupMult @U1 saj sq, hom) of
        (Absent, _) -> denseBlocks rest sq hom (off + stride)
        (Present {}, InterNil) -> []
        (Present (_ :: Proxy n), InterCons blk homRest) ->
          ( targetIrrepOffset @U1 saj sq,
            off,
            unwrap (expandBlock @U1 (Proxy @j) blk)
          )
            : denseBlocks rest sq homRest (off + stride)
denseBlocks (SRepConsSU2 @j @m saj rest) sq hom off =
  let stride :: Int
      stride = fromIntegral (natVal (Proxy @(SectorDim SU2 j m)))
   in case (sLookupMult @SU2 saj sq, hom) of
        (Absent, _) -> denseBlocks rest sq hom (off + stride)
        (Present {}, InterNil) -> []
        (Present (_ :: Proxy n), InterCons blk homRest) ->
          ( targetIrrepOffset @SU2 saj sq,
            off,
            unwrap (expandBlock @SU2 (Proxy @j) blk)
          )
            : denseBlocks rest sq homRest (off + stride)

renderDenseMatrix :: Int -> Int -> [BlockStamp] -> String
renderDenseMatrix rows cols stamps =
  let zero = LA.konst 0 (rows, cols) :: LA.Matrix (Complex Double)
      stamped =
        foldl
          ( \acc (r0, c0, blk) ->
              let (br, bc) = LA.size blk
                  rowsAcc = LA.toLists acc
                  rowsBlk = LA.toLists blk
               in LA.fromLists
                    [ if ri >= r0 && ri < r0 + br
                        then
                          let brow = rowsBlk !! (ri - r0)
                           in [ if ci >= c0 && ci < c0 + bc
                                  then brow !! (ci - c0)
                                  else rowsAcc !! ri !! ci
                              | ci <- [0 .. cols - 1]
                              ]
                        else rowsAcc !! ri
                    | ri <- [0 .. rows - 1]
                    ]
          )
          zero
          stamps
   in unlines
        [ "Dense forgetful matrix (" ++ show rows ++ "×" ++ show cols ++ "), block-diagonal:",
          prettyMat stamped
        ]
