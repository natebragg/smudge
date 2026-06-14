-- Copyright 2026 Nate Bragg.
-- This software is released under the 3-Clause BSD License.
-- The license can be viewed at https://github.com/smudgelang/smudge/blob/master/LICENSE

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Language.Smudge.Semantics.Ty (
  Ty(..),
  SymbolTable(..),
  elaborate,
  Resolution(..),
) where

import Language.Smudge.Grammar (
    StateMachine(StateMachine),
    Event(Event, EventEnter, EventExit),
    Function(FuncVoid, FuncEvent),
    SideEffect(SideEffect),
    EventHandler,
    WholeState,
    )
import Language.Smudge.Semantics.Model (
    TaggedName,
    )

import Data.List (intercalate)
import Data.Set (Set, intersection, union, difference)
import qualified Data.Set as Set(empty, singleton)
import Data.Map.Ordered (OMap, unionWithL, intersectionWith, assocs, toAscList, (\\))
import qualified Data.Map.Ordered as Map(empty, lookup, singleton, fromList)
import Data.Maybe (fromMaybe)
import Data.Foldable (toList)
import Control.Monad.State (StateT, MonadState, evalStateT, get, put)
import Control.Monad.Except (Except, throwError)
import Control.Monad.Trans.Class (lift)
import Control.Monad (foldM, when)

type Env = OMap TaggedName Ty

type Envar = String

type Capvar = String

data Ty = Tyvar (Maybe Ty) String
        | Ty TaggedName
        | Cap (Maybe Capvar) (Set TaggedName)
        | Ty :-> Ty
        | Product [Ty]
        | Record Env
        | Variant (Maybe Envar) Env
    deriving (Show, Eq, Ord)

infixr 8 :->

prettyField :: (TaggedName, Ty) -> String
prettyField (x, tau) = show x ++ ": " ++ pretty tau

pretty :: Ty -> String
pretty (Tyvar tau x) = x ++ case tau of Nothing -> ""; Just tau -> "^(" ++ pretty tau ++ "?)"
pretty (Ty x) = show x
pretty (Cap Nothing xs) | null xs = "uneventful"
pretty (Cap Nothing xs) = intercalate ", " $ map (("eventful " ++) . show) (toList xs)
pretty (Cap (Just p) xs) = intercalate ", " $ p : map (("eventful " ++) . show) (toList xs)
pretty (tau1 :-> tau2) = pretty tau1 ++ " -> " ++ pretty tau2
pretty (Product []) = "void"
pretty (Product [x]) = pretty x
pretty (Product xs) = "(" ++ intercalate ", " (map pretty xs) ++ ")"
pretty (Record gamma) = "(" ++ intercalate ", " (map prettyField $ assocs gamma) ++ ")"
pretty (Variant Nothing gamma) = "{" ++ intercalate ", " (map prettyField $ toAscList gamma) ++ "}"
pretty (Variant (Just g) gamma) | null gamma = g
pretty (Variant (Just g) gamma) = "{" ++ intercalate ", " (map prettyField $ toAscList gamma) ++ "} + " ++ g

newtype SymbolTable = SymbolTable Env
    deriving (Show, Eq, Ord)

data Constraint = Trivial
                | Ty :~: Ty
                | Ty `EqRange` Ty
                | Constraint :/\ Constraint

isTrivial Trivial = True
isTrivial _ = False

infixl 7 :~:
infixl 7 `EqRange`
infixl 6 :/\

instance Semigroup Constraint where
    Trivial <> c = c
    c <> Trivial = c
    c1 <> c2 = c1 :/\ c2

instance Monoid Constraint where
    mempty = Trivial

type TypeError = String

disjUnion :: (Ord k, Show k, Eq v) => OMap k v -> OMap k v -> OMap k v
disjUnion = unionWithL eqOrFail
    where eqOrFail k v1 v2 =
              if v1 == v2 then v1
              else error $ "Found conflicting values for " ++ (show k) ++ "\n"

lookupDef :: (Ord k) => v -> k -> OMap k v -> v
lookupDef d k m = case Map.lookup k m of Nothing -> d; Just v -> v

keys :: OMap k v -> [k]
keys = map fst . assocs

ksvs :: OMap k v -> ([k], [v])
ksvs = unzip . toAscList

instance (Ord k, Show k, Eq v) => Semigroup (OMap k v) where
    (<>) = disjUnion

instance (Ord k, Show k, Eq v) => Monoid (OMap k v) where
    mempty = Map.empty

foldMapM f xs = mconcat <$> traverse f xs

foreignFns :: (StateMachine TaggedName, [(WholeState TaggedName)]) -> [TaggedName]
foreignFns (_, ss) = concat $ map goWS ss
    where goWS (_, _, ens, ehs, exs) = concat $ map goSE ens ++ map goEH ehs ++ map goSE exs
          goEH (_, ses, _) = concat $ map goSE ses
          goSE (SideEffect f args) = concat $ map goF $ f : args
          goF (FuncVoid f) = [f]
          goF _ = []

freshVar :: (Num i, Show i, MonadState i m) => String -> m String
freshVar x = do n <- get
                put (n + 1)
                return $ x ++ show n

freshTyvar :: (Num i, Show i, MonadState i m) => m String
freshTyvar = freshVar "a"

freshEnvar :: (Num i, Show i, MonadState i m) => m String
freshEnvar = freshVar "g"

freshCapvar :: (Num i, Show i, MonadState i m) => m String
freshCapvar = freshVar "p"

elaborate :: Resolution -> SymbolTable -> [(StateMachine TaggedName, [(WholeState TaggedName)])] -> Except TypeError SymbolTable
elaborate res (SymbolTable gamma) ms =
    flip evalStateT 0 $
        do let sig = Map.empty
               fs = concat $ map foreignFns ms
           g_d <- Map.fromList <$> (flip traverse fs $ \f -> (,) f <$> Tyvar Nothing <$> freshTyvar)
           let gamma' = disjUnion gamma g_d
           (cs, tau) <- infer sig gamma' ms
           theta <- unify cs
           gamma' <- lift $ close $ subst theta gamma'
           tau    <- lift $ close $ subst theta tau
           let (Record gamma_tau) = tau
           SymbolTable <$> lift (resolve res $ disjUnion gamma' gamma_tau)

class Infer x where
    infer :: (Num i, Show i, MonadState i m) => Env -> Env -> x -> m (Constraint, Ty)

instance Infer [(StateMachine TaggedName, [(WholeState TaggedName)])] where
    infer sig gamma ms =
        do alphas <- flip traverse ms $ \_ -> Tyvar Nothing <$> freshTyvar
           let xs = flip map ms $ \(StateMachine x, _) -> x
               sig' = Map.fromList $ zip xs alphas
               sig'' = disjUnion sig sig'
               g_m = Map.fromList $ zip xs $ map Ty xs
           let gamma' = disjUnion gamma g_m
           c <- flip foldMapM (zip ms alphas) $ \(m_i, alpha_i) -> do
                  (c_i, tau_i) <- infer sig'' gamma' m_i
                  return $ c_i <> alpha_i :~: tau_i
           return (c, Record sig')

instance Infer (StateMachine TaggedName, [(WholeState TaggedName)]) where
    infer sig gamma (_, qs) =
        do alpha <- Tyvar Nothing <$> freshTyvar
           c <- flip foldMapM qs $ \q_i -> do
                  (c_i, tau_i) <- infer sig gamma q_i
                  let Variant Nothing g_i = tau_i
                  g_i' <- freshEnvar
                  return $ c_i <> Variant (Just g_i') g_i :~: alpha
           return (c, alpha)

instance Infer (WholeState TaggedName) where
    infer sig gamma (_, _, ens, ehs, exs) =
        -- One odd behavior here is that anyevent is dropped; morally, this should
        -- be included in the type, but that would lead to the problem being in
        -- gflat(2), and we never act on the state's type anyhow, so we can cheat.
        -- To be more accurate, match the any event with a new envar, pull this
        -- out, then conditionally match in the state machine level
        do (c, g_q) <- flip foldMapM ehs $ \eh_i -> do
                         (c_i, tau_i) <- infer sig gamma eh_i
                         let a = case eh_i of (Event a , _, _) -> Just a; _ -> Nothing
                             g_q_i = Map.singleton <$> flip (,) tau_i <$> a
                         return (c_i, g_q_i)
           c_en <- flip foldMapM ens $ \d_i -> fst <$> infer sig gamma (EventEnter :: Event TaggedName, d_i)
           c_ex <- flip foldMapM exs $ \d_i -> fst <$> infer sig gamma (EventExit  :: Event TaggedName, d_i)
           let ty = Variant Nothing $ fromMaybe Map.empty g_q
           return (c_en <> c <> c_ex, ty)

instance Infer (EventHandler TaggedName) where
    infer sig gamma (a, ds, _) =
        do let g_a = Map.empty
               gamma' = disjUnion gamma g_a
           c <- flip foldMapM ds $ \d_i -> do
                  (c_i, phi_i) <- infer sig gamma' (a, d_i)
                  return c_i
           let ty = Record g_a :-> Cap Nothing Set.empty
           return (c, ty)

instance Infer (Event TaggedName, SideEffect TaggedName) where
    infer sig gamma (a, SideEffect f args) =
        do (c_d, tau_d) <- infer sig gamma (a, f)
           (c, taus) <- flip foldMapM args $ \e_i -> do
                          (c_i, tau_i) <- infer sig gamma (a, e_i)
                          return (c_i, [tau_i])
           psi <- freshCapvar
           let ty = Cap (Just psi) Set.empty
               cs = tau_d :~: Product taus :-> ty <> c_d <> c
           return (cs, ty)

instance Infer (Event TaggedName, Function TaggedName) where
    infer sig gamma (_, FuncEvent (StateMachine x_m, Event x_a)) =
        do let Just tau = Map.lookup x_m sig
           g <- freshEnvar
           alpha_a  <- Tyvar (Just $ Record Map.empty) <$> freshTyvar
           alpha_pi <- Tyvar Nothing <$> freshTyvar
           let g_a = Map.singleton (x_a, alpha_a :-> Cap Nothing Set.empty)
               c = Variant (Just g) g_a :~: tau :/\ alpha_pi `EqRange` alpha_a
               ty = alpha_pi :-> Cap Nothing (Set.singleton x_a) -- x_a here is a hack around the current code gen
           return (c, ty)
    infer sig gamma (a, FuncVoid f) =
        do alpha  <- Tyvar (Just $ Product []) <$> freshTyvar
           psi <- freshCapvar
           let Just tau = Map.lookup f gamma
               -- TODO what about EventAny? This leads to first.smudge inferring the wrong type for @sideEffect
               cap_x = case a of Event x -> Set.singleton x; _ -> Set.empty
               c = tau :~: alpha :-> Cap (Just psi) cap_x
           return (c, tau)

type Substitution = OMap String Ty

unify :: Constraint -> StateT Int (Except TypeError) Substitution
unify = go
    where partRange (c1 :/\ c2) = partRange c1 <> partRange c2
          partRange c@(_ `EqRange` Record _) = (c, Trivial)
          partRange c@(_ `EqRange` _) = (Trivial, c)
          partRange c = (c, Trivial)
          catEnv theta = disjUnion theta . subst theta
          goPairs :: [Ty] -> [Ty] -> StateT Int (Except TypeError) Substitution
          goPairs ts1 ts2 = go $ mconcat $ zipWith (:~:) ts1 ts2
          go' (c1 :/\ c2) =
              do theta_1 <- go' c1
                 theta_2 <- go' $ subst theta_1 c2
                 return $ catEnv theta_2 theta_1
          go' c = go c
          go c@(_ :/\ _) = go' $ uncurry (:/\) $ partRange c
          go Trivial = return Map.empty
          go (tau1 `EqRange` Record gamma) = go $ tau1 :~: Product (toList gamma)
          go (tau1 `EqRange` Tyvar (Just tau2) _) = go $ tau1 `EqRange` tau2
          go (_ `EqRange` _) = throwError $ "Found unsatisfiable range constraint.\n"
          go (tau1 :~: tau2) | tau1 == tau2 = return Map.empty
          go (Tyvar _ alpha :~: tau2) | not (freein alpha tau2) = return $ Map.singleton (alpha, tau2)
          go (tau1 :~: tau2@(Tyvar _ _)) = go $ tau2 :~: tau1
          go (tau1 :-> tau2 :~: tau3 :-> tau4) = go $ tau1 :~: tau3 :/\ tau2 :~: tau4
          go (Product taus1 :~: Product taus2) | length taus1 == length taus2 = goPairs taus1 taus2
          go (Record gamma1 :~: Record gamma2) | keys gamma1 == keys gamma2 = goPairs (toList gamma2) (toList gamma2)
          go (t1@(Cap Nothing _) :~: t2@(Cap (Just _) _)) = go $ t2 :~: t1
          go (Cap (Just p) xs :~: Cap Nothing ys) | null $ difference xs ys = return $ Map.singleton (p, Cap Nothing $ difference ys xs)
          go (Cap (Just p_x) xs :~: Cap (Just p_y) ys) | p_x /= p_y =
              do p_z <- freshCapvar
                 let tau_x = Cap (Just p_z) $ difference ys xs
                     tau_y = Cap (Just p_z) $ difference xs ys
                 return $ Map.fromList [(p_x, tau_x), (p_y, tau_y)]
          go (Variant Nothing (ksvs -> (xks, xvs)) :~: Variant Nothing (ksvs -> (yks, yvs))) | xks == yks = goPairs xvs yvs
          go (t1@(Variant Nothing _) :~: t2@(Variant (Just _) _)) = go $ t2 :~: t1
          go (Variant (Just g) gamma_x :~: Variant Nothing gamma_y) | null (gamma_x \\ gamma_y) =
              do let tau_y_no_x = Variant Nothing $ gamma_y \\ gamma_x
                 go $ Tyvar Nothing g :~: tau_y_no_x <> mconcat (toList $ intersectionWith (const (:~:)) gamma_x gamma_y)
          go (Variant (Just g_x) gamma_x :~: Variant (Just g_y) gamma_y) | g_x == g_y = go $ Variant Nothing gamma_x :~: Variant Nothing gamma_y
          go (Variant (Just g_x) gamma_x :~: Variant (Just g_y) gamma_y) =
              do g_z <- freshEnvar
                 let tau_x_no_y = Variant (Just g_z) $ gamma_x \\ gamma_y
                     tau_y_no_x = Variant (Just g_z) $ gamma_y \\ gamma_x
                 go $ Tyvar Nothing g_x :~: tau_y_no_x <> Tyvar Nothing g_y :~: tau_x_no_y <> mconcat (toList $ intersectionWith (const (:~:)) gamma_x gamma_y)
          go (tau1 :~: tau2) = throwError $ "Cannot unify types:\n    " ++ pretty tau1 ++ "\n    " ++ pretty tau2 ++ "\n"

freein :: String -> Ty -> Bool
freein x (Tyvar _ y) = x == y
freein x (Cap (Just p) _) = x == p
freein x (tau1 :-> tau2) = freein x tau1 || freein x tau2
freein x (Product taus) = any (freein x) taus
freein x (Record gamma) = any (freein x) (toList gamma)
freein x (Variant (Just g) gamma) = x == g || any (freein x) (toList gamma)
freein x _ = False

class Subst a where
    subst :: Substitution -> a -> a

instance Subst Ty where
    subst theta = go
        where go tau@(Tyvar _ alpha)      = lookupDef tau alpha theta
              go tau@(Ty x)               = tau
              go tau@(Cap Nothing    cs)  = tau
              go tau@(Cap (Just psi) cs)  = case Map.lookup psi theta of
                                              Nothing -> tau
                                              Just (Cap p cs') -> Cap p $ union cs' cs
              go (tau1 :-> tau2)          = go tau1 :-> go tau2
              go (Product taus)           = Product $ subst theta taus
              go (Record gamma)           = Record $ subst theta gamma
              go (Variant Nothing  gamma) = Variant Nothing $ subst theta gamma
              go (Variant (Just g) gamma) = case Map.lookup g theta of
                                              Nothing -> Variant (Just g) $ subst theta gamma
                                              Just (Variant g gamma') -> Variant g $ disjUnion gamma' $ subst theta gamma

instance Subst Constraint where
    subst theta Trivial = Trivial
    subst theta (tau1 :~: tau2) = subst theta tau1 :~: subst theta tau2
    subst theta (tau1 `EqRange` tau2) = subst theta tau1 `EqRange` subst theta tau2
    subst theta (c1 :/\ c2) = subst theta c1 <> subst theta c2

instance (Functor f, Subst v) => Subst (f v) where
    subst theta = fmap (subst theta)

class Close a where
    close :: a -> Except TypeError a

instance Close Ty where
    close (Tyvar Nothing    a) = throwError $ "Could not solve for type variable" ++ a ++ "\n"
    close (Tyvar (Just tau) _) = return $ tau
    close tau@(Ty x)        = return $ tau
    close (Cap _ cs)        = return $ Cap Nothing cs
    close (tau1 :-> tau2)   = (:->) <$> close tau1 <*> close tau2
    close (Product taus)    = Product <$> close taus
    close (Record gamma)    = Record <$> close gamma
    close (Variant _ gamma) = Variant Nothing <$> close gamma

instance (Traversable t, Close v) => Close (t v) where
    close = traverse close

data Resolution = Strict | Permissive | Passthrough
    deriving (Eq)

class Resolve a where
    resolve :: Resolution -> a -> Except TypeError a

instance Resolve Ty where
    resolve Passthrough tau       = return $ tau
    resolve r tau@(Tyvar _ _)     = return $ tau
    resolve r tau@(Ty _)          = return $ tau
    resolve r tau@(Cap _ cs) | length cs <= 1 = return $ tau
    resolve Strict     (Cap _ cs) = throwError $ "Could not strictly resolve function used in multiple contexts:\n    " ++ show cs ++ "\n"
    resolve Permissive (Cap p  _) = return $ Cap p Set.empty
    resolve r (tau1 :-> tau2)     = (:->) <$> resolve r tau1 <*> resolve r tau2
    resolve r (Product taus)      = Product <$> resolve r taus
    resolve r (Record gamma)      = Record <$> resolve r gamma
    resolve r (Variant _ gamma)   = Variant Nothing <$> resolve r gamma

instance (Traversable t, Resolve v) => Resolve (t v) where
    resolve = traverse . resolve
