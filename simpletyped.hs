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
  Var :: Typeable a => Int -> Expr a
  Lib :: Typeable a => String -> Expr a
  Lam :: Typeable a => String -> Expr β -> Expr (a -> β)
  Lpp :: (Typeable α, Typeable β) => Expr (α -> β) -> Expr α -> Expr β
  deriving (Typeable)

instance Eq (Expr a) where
  Var x == Var y = x == y
  Lib x == Lib y = x == y
  (Lam x e1) == (Lam y e2) = x == y && e1 == e2
  (Lpp e1 e2) == (Lpp e3 e4) = e1 == (unsafeCoerce e3) && e2 == (unsafeCoerce e4)
  _ == _ = False

instance Show (Expr a) where
  show (Var x) = show x
  show (Lib x) = show x
  show (Lam x e) = "λ" ++ show x ++ "." ++ show e
  show (Lpp e1 e2) = "Lpp " ++ show e1 ++ " " ++ show e2

data Definition where
  Def :: forall α. Typeable α => String -> Expr α -> Definition

instance Show Definition where
  show (Def x e) = show x ++ " = " ++ show e

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
isType :: (Typeable α, Typeable β) => TypeSingleton α -> Expr β -> Maybe (α :~~: β)
isType f s =
  let a = typeOf (getTS f)
      b = typeOf (getExprT s) in
  eqTypeRep a b

lookupDefinition :: Typeable α => String -> TypeSingleton α -> [Definition] -> Maybe (Expr α)
lookupDefinition var _ [] = Nothing
lookupDefinition var t ((Def var' t'):ds)
  | var == var' = let res = isType t t' in
    case res of
      Just HRefl -> Just t'
      Nothing -> lookupDefinition var t ds
  | otherwise = lookupDefinition var t ds


-- Substitution {- TODO Figure out substitution and β-redex -}
subst :: Expr α -> Expr β -> Int -> Expr α
subst (Var n) t c
  | c == n = unsafeCoerce t
  | otherwise = Var n
subst (Lib n) t c = Lib n
subst (Lpp t₀ t₁) t c = Lpp (subst t₀ t c) (subst t₁ t c)
subst (Lam var t) t' c = Lam var $ subst t t' (c + 1)

-- Application
--app :: Expr (α -> β) -> Expr α -> Expr β
--app (Lam var t) t' = (1 ↓ 0) $ subst t ((0 ↑ 1) t') 0

-- β-redex
betaRedex :: Expr α -> [Definition] -> Expr α
betaRedex (Lpp (Lam var t) t') _ = (1 ↓ 0) $ subst t ( ( 1 ↑ 0 ) t' ) 0
betaRedex (Lpp t₀ t₁) defs_ = Lpp (betaRedex t₀ defs_) (betaRedex t₁ defs_)
betaRedex (Lam var t) defs_ = Lam var $ betaRedex t defs_
betaRedex (Lib n) defs = 
  let yy = TS $ getExprT $ Lib n
      res = lookupDefinition n yy defs in
  case res of
    Just t -> betaRedex t defs
    Nothing -> Lib n
betaRedex t _ = t

betaApply :: Expr α -> [Definition] -> Expr α
betaApply x defs_ = let u = betaRedex x defs_ in
  if u == x then x else betaApply u defs_

-- Lambda defs
-- λx.λy.x :: Bool
false :: Expr Bool
false = unsafeCoerce (Lam "x" (Lam "y" (Var 0 :: Expr Bool) :: Expr (Bool -> Bool)) :: Expr (Bool -> Bool -> Bool))
true :: Expr Bool
true = unsafeCoerce (Lam "x" (Lam "y" (Var 1 :: Expr Bool) :: Expr (Bool -> Bool)) :: Expr (Bool -> Bool -> Bool))
if_ :: Typeable α => Expr (Bool -> α -> α -> α)
if_ = unsafeCoerce $ (Lam "val" (Var 0 :: Expr Bool) :: Expr (Bool -> Bool))
------ Test cases ------
defs :: [Definition]
defs = [Def "true" true,
        Def "false" false,
        Def "if" if_] -- This doesn't work, and it's NOT supposed to. 
                      -- If it was working, it would be a polymorphic function, 
                      -- but this is supposed to be a Simple Typed Lambda Calculus.
                      -- So, it's not supposed to work.
                      -- But I think everything else is working.
                      -- Anyways, cheers.

-- List of definitions

builderDef :: Typeable α => String -> Expr α -> Definition
builderDef a b = Def a b


test = Fun (typeOf (1 :: Int)) (typeOf True)



