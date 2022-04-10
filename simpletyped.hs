{-
Copyright (C) 2022  Iván Molina Rebolledo
This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.
This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.
You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>. 
-}

{-# LANGUAGE DataKinds, GADTSyntax, TypeFamilies, TypeOperators  #-}

import Type.Reflection
import Unsafe.Coerce (unsafeCoerce)




data Expr a where
  Val :: a -> Expr a
  Var :: Int -> Expr a
  Lib :: String -> Expr a
  Lam :: String -> Expr α -> Expr (a -> β)
  Lpp :: Expr (α -> β) -> Expr α -> Expr β
  deriving Typeable

data Definition α where
  Def :: forall α. Typeable α => String -> Expr α -> Definition α

data Definable where
  Definable :: Typeable α => Definition α -> Definable

data TypeSingleton a where
  TS :: a -> TypeSingleton a
  Holder :: TypeSingleton a

(↑) :: Int -> Int -> Expr α -> Expr α
(d ↑ c) (Var n)
  | c <= n = Var (n - 1)
  | otherwise = Var n
(d ↑ c) (Lib n) = Lib n
(d ↑ c) (Lpp t₀ t₁) = Lpp ((d ↑ c) t₀) ((d ↑ c) t₁)
(d ↑ c) (Lam τ t) = Lam τ $ ((d ↑) $ c + 1) t

(↓) :: Int -> Int -> Expr α -> Expr α
(d ↓ c) (Var n)
  | c <= n = Var (n - 1)
  | otherwise = Var n
(d ↓ c) (Lib n) = Lib n
(d ↓ c) (Lpp t₀ t₁) = Lpp ((d ↓ c) t₀) ((d ↓ c) t₁)
(d ↓ c) (Lam var t) = Lam var $ ((d ↓) $ c - 1) t

-- Get empty type from Expr
getExprT :: Expr a -> a
getExprT e = unsafeCoerce e

-- Get empty type from TypeSingleton
getTS :: TypeSingleton a -> a
getTS (TS a) = a

-- Is the same type as the one in the definition
isType :: (Typeable α, Typeable β, α ~ β) => TypeSingleton α -> Expr β -> Maybe (α :~~: β)
isType f s =
  let a = typeOf (getTS f)
      b = typeOf (getExprT s) in
  eqTypeRep a b


lookupDefinition :: String -> TypeSingleton α -> [Definition α] -> Maybe (Expr α)
lookupDefinition var _ [] = Nothing
lookupDefinition var t ((Def var' t'):ds)
  | var == var' = let res = isType t t' in
    case res of
      Just HRefl -> Just t'
      Nothing -> lookupDefinition var t ds
  | otherwise = lookupDefinition var t ds


------ Test cases ------

-- List of definitions

builderDef :: Typeable α => String -> Expr α -> Definable
builderDef a b = Definable $ Def a b

defs :: [Definable]
defs = [
  builderDef "false" $ Val False,
  builderDef "true" $ Val True,
  builderDef "zero" $ Val (0 :: Int)
  ]

infere = Lam "n" $ Val False

test = Fun (typeOf (1 :: Int)) (typeOf True)



