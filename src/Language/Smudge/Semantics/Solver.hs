-- Copyright 2026 Nate Bragg.
-- This software is released under the 3-Clause BSD License.
-- The license can be viewed at https://github.com/smudgelang/smudge/blob/master/LICENSE

{-# LANGUAGE TypeFamilies #-}

module Language.Smudge.Semantics.Solver (
    Ty(Void, Ty, (:->)),
    Binding(..),
    adaptTable,

    SymbolTable(..),
    filterBind,
) where

import Language.Smudge.Semantics.Model (
    qualify,
    TaggedName,
    Tagged(..),
    )
import Language.Smudge.Semantics.Basis (
    machineExports,
    machineExternals
    )
import qualified Language.Smudge.Semantics.Ty as T (
    Capability(..),
    uncaps,
    Ty(..),
    SymbolTable(..)
    )
import Language.Smudge.Passes.Passes (AbstractFoldable(..))

import Data.Map (Map, fromList, foldrWithKey)
import qualified Data.Map as Map(filter)
import qualified Data.Map.Ordered as OMap(assocs)
import qualified Data.Set as Set(empty, singleton, union, foldr)
import Data.Foldable (toList)

data Binding = External | Unresolved | Exported | Internal
    deriving (Show, Eq, Ord)

data Ty = Void
        | Ty TaggedName
        | Ty :-> Ty
    deriving (Eq, Ord)

instance Show Ty where
    show = go False
        where go _ Void = "void"
              go _ (Ty n) = show $ qualify n
              go True (tau :-> tau') = "(" ++ go True tau ++ " -> " ++ show tau' ++ ")"
              go False (tau :-> tau') = go True tau ++ " -> " ++ show tau'

infixr 7 :->

newtype SymbolTable = SymbolTable (Map TaggedName (Binding, Ty))
    deriving (Show, Eq, Ord)

instance AbstractFoldable SymbolTable where
    type FoldContext SymbolTable = (TaggedName, (Binding, Ty))
    afold f a (SymbolTable gamma) = foldrWithKey (curry f) a gamma

filterBind :: SymbolTable -> Binding -> SymbolTable
filterBind (SymbolTable gamma) b = SymbolTable $ Map.filter (\(b', _) -> b == b') gamma

adaptTable :: T.SymbolTable -> SymbolTable
adaptTable (T.SymbolTable gamma) = SymbolTable $ fromList $ goEnv gamma
    where goTy (T.Product taus T.:-> T.Cap Nothing cs) = goFunTy (goCaps cs ++ taus) Void
          goTy (T.Product taus T.:-> T.Ty x) = goFunTy taus $ Ty x
          goTy (T.Ty x) = Ty x
          goTy tau = error $ "Got untranslatable type " ++ show tau ++ ".  This is a bug in smudge.\n"
          goCaps = toList . Set.foldr (Set.union . goCap) Set.empty . T.uncaps
          goCap (T.Eventful x) = Set.singleton $ T.Ty x
          goFunTy [] ret = Void :-> ret
          goFunTy tys ret = foldr (:->) ret $ map goTy tys
          goEnv = concatMap go . OMap.assocs
          go (x@(TagFunction _), tau) = [(x, (External, goTy tau))]
          go (x@(TagEvent    q), tau) = [(x, (Exported, Ty x)), (TagFunction q, (Exported, Ty x :-> Void))]
          go (x@(TagMachine  _), T.Variant Nothing gamma) = goEnv gamma ++ xps ++ xts
              where xps = map (fmap $ (,) Exported . goTy) $ machineExports x
                    xts = map (fmap $ (,) External . goTy) $ machineExternals x
