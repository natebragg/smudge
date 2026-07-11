-- Copyright 2026 Nate Bragg.
-- This software is released under the 3-Clause BSD License.
-- The license can be viewed at https://github.com/smudgelang/smudge/blob/master/LICENSE

module Language.Smudge.Semantics.Basis (
    basisAlias,
    machineExports,
    machineExternals,
    basis,
) where

import Language.Smudge.Semantics.Ty (
    Ty(Ty, Product, Cap, (:->)),
    SymbolTable(..)
    )
import Language.Smudge.Semantics.Model (
  QualifiedName,
  qualify,
  TaggedName,
  Tagged(..),
  )
import Language.Smudge.Semantics.Alias (Alias, rename)

import Data.Map (fromList)
import qualified Data.Map.Ordered as OMap(fromList)

basisAlias :: String -> Alias QualifiedName
basisAlias "" = mempty
basisAlias namespace = fromList $ map q [
            -- add more here
            "debug_print",
            "free",
            "panic_print",
            "panic"]
    where q n = (qualify n, qualify(namespace, n))

void :: Ty
void = Ty $ TagBuiltin $ qualify "void"

str :: Ty
str = Ty $ TagBuiltin $ qualify "char"

wrapper_name :: TaggedName -> TaggedName
wrapper_name m = TagState $ qualify (m, "Event_Wrapper")

wrapper :: TaggedName -> Ty
wrapper = Ty . wrapper_name

machineExports :: TaggedName -> [(TaggedName, Ty)]
machineExports m = runtime
    where
          runtime = [
            -- add more sm-specific exports here
            (TagFunction $ qualify (m, "Free_Message"),       Product [wrapper m] :-> Cap Nothing mempty),
            (TagFunction $ qualify (m, "Handle_Message"),     Product [wrapper m] :-> Cap Nothing mempty),
            (TagFunction $ qualify (m, "Current_state_name"), Product [] :-> str)]

machineExternals :: TaggedName -> [(TaggedName, Ty)]
machineExternals m = runtime
    where runtime = [
            -- add more sm-specific externals here
            (TagFunction $ qualify (m, "Send_Message"),       Product [wrapper m] :-> Cap Nothing mempty)]

basis :: Alias QualifiedName -> SymbolTable
basis aliases = runtime
    where rename' = rename aliases . qualify
          runtime = SymbolTable $ OMap.fromList [
            -- add more smudge-wide externals here
            (TagFunction $ rename' "debug_print", Product [str, str, str] :-> Cap Nothing mempty),
            (TagFunction $ rename' "free",        Product [void] :-> Cap Nothing mempty),
            (TagFunction $ rename' "panic_print", Product [str, str, str] :-> Cap Nothing mempty),
            (TagFunction $ rename' "panic",       Product [] :-> Cap Nothing mempty)]
