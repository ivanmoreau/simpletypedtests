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






data Expr a where
  Var :: Int -> Expr a
  Lib :: String -> Expr a
  Lam :: String -> Expr α -> Expr (a -> β)
  App :: Expr (α -> β) -> Expr α -> Expr β

data Definition a where
  Def :: String -> Expr a -> Definition a

data TypeSingleton a where
  TS :: a -> TypeSingleton a
  Holder :: TypeSingleton a

-- Intencional equality
data (≡) a b where
  Refl :: a ≡ a

(↑) :: Int -> Int -> Expr α -> Expr α
(d ↑ c) (Var n)
  | c <= n = Var (n - 1)
  | otherwise = Var n
(d ↑ c) (Lib n) = Lib n
(d ↑ c) (App t₀ t₁) = App ((d ↑ c) t₀) ((d ↑ c) t₁)
(d ↑ c) (Lam τ t) = Lam τ $ ((d ↑) $ c + 1) t

(↓) :: Int -> Int -> Expr α -> Expr α
(d ↓ c) (Var n)
  | c <= n = Var (n - 1)
  | otherwise = Var n
(d ↓ c) (Lib n) = Lib n
(d ↓ c) (App t₀ t₁) = App ((d ↓ c) t₀) ((d ↓ c) t₁)
(d ↓ c) (Lam var t) = Lam var $ ((d ↓) $ c - 1) t

ts2Holder :: TypeSingleton a -> TypeSingleton a
ts2Holder (TS a) = Holder

expr2Holder :: Expr a -> TypeSingleton a
expr2Holder (Var _) = Holder

lookupDefinition :: String -> TypeSingleton α -> [Definition α] -> Maybe (Expr α)
lookupDefinition var (TS t) [] = Nothing
lookupDefinition var (TS t) ((Def var' t'):ds)
  | var == var' = let et = expr2Holder t' in
    if et == Holder then Just t' else Nothing
  | otherwise = lookupDefinition var (TS t) ds




