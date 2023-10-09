module RA where

open import Data.Bool.Base  using (Bool; if_then_else_)
open import Data.List.Base  using (_∷_ ; [] ; List ; length ; foldr ; intersperse ; map)
open import Data.Nat.Base   using (ℕ; _+_)
open import Data.String     using (_++_ ; toList ; String ; _==_)
open import Data.BoundedVec using (BoundedVec) renaming ([] to ⟨⟩ ; _∷_ to _::_)
open import Function.Base   using (const ; _∘_)
open import Data.Product    using (proj₁)
import Data.List.Base as List

open import DataTypes
import Parse as P

-- Convert a list to a bounded vector of any length ≥ the length
-- of the given list.
-- This is useful for creating strings that look like they came
-- from the database.
mkBounded : {A : Set} {n : ℕ} → (l : List A) → BoundedVec A (length l + n)
mkBounded []       = ⟨⟩
mkBounded (x ∷ xs) = x :: mkBounded xs

-- This is a little convoluted, but we want to hide
-- the constructor for the handle data type.
-- A user should not be able to construct a handle
-- except through the interface provided below, which
-- involves runtime checking of the given schema
private
    data Handle′ : Schema → Set where
      handle : (s : Schema) → String → Handle′ s

open Handle′ public hiding (handle)

Handle : Schema → Set
Handle = Handle′

data Expr : Schema → U → Set where
  -- A string literal can be have any length up to the maximum length
  -- that is valid for the given field.
  Lit  : ∀ {s n} → (nm : String) → Expr s (STR (length (toList nm) + n))
  _:=_ : ∀ {u s} → Expr s u → Expr s u → Expr s BOOL
  _:<_ : ∀ {u s} → Expr s u → Expr s u → Expr s BOOL
  -- Select a value in the schema
  _!_  : (s : Schema) → (nm : String) → { p : So (occurs nm s) } → Expr s (lookup nm s p)

data RA : Schema → Set where
  Read    : {s : Schema} → Handle s → RA s
  Union   : {s : Schema} → RA s → RA s → RA s
  Diff    : {s : Schema} → RA s → RA s → RA s
  Product : {s s′ : Schema} → {p : So (disjoint s s′)} → RA s → RA s′ → RA (s List.++ s′)
  Project : ∀ {s} → (s′ : Schema) → {p : So (sub s′ s)} → RA s → RA s′
  Select  : {s : Schema} → Expr s BOOL → RA s → RA s

enquote : String → String
enquote x = "\"" ++ x ++ "\""

columnNames : Schema → String
columnNames = foldr _++_ "" ∘ intersperse ","  ∘ map proj₁

mutual

  showExpr : ∀ {s u} → Expr s u → String
  showExpr (Lit nm)  = enquote nm
  showExpr (e := e₁) = showExpr e ++ " = " ++ showExpr e₁
  showExpr (e :< e₁) = showExpr e ++ " < " ++ showExpr e₁
  showExpr (s ! nm)  = nm

  -- Compile a relational algebra statement into
  toSQL : ∀ {s} → RA s → String
  toSQL (Read (handle s x)) = "select " ++ columnNames s ++ " from " ++ x
  toSQL (Union x x₁)        = "select * from (" ++ toSQL x ++ ") union all " ++ toSQL x₁
  toSQL (Diff x x₁)         = let l = toSQL x
                                  r = toSQL x₁
                              in "select * from (" ++ l ++ " except " ++ r ++ ") union all "
                               ++ "select * from (" ++ r ++ " except " ++ l ++ ")"
  toSQL (Product x x₁) = "select * from (" ++ toSQL x ++ ") inner join (" ++ toSQL x₁ ++ ")"
  toSQL (Project s x)  = "select " ++ columnNames s ++ " from (" ++ toSQL x ++ ")"
  toSQL (Select x x₁)  = toSQL x₁ ++ " where (" ++ showExpr x ++ ")"

-- These are the functions that interface with the database create
-- handles and execute queries.

{-# FOREIGN GHC import Database #-}
open import IO.Primitive
-- import Foreign.Haskell as Hask

postulate runQuery : String → IO String
postulate dbDescription : String → IO String
postulate abort : ∀ {A : Set} → IO A
{-# COMPILE GHC runQuery      = Database.runQuery #-}
{-# COMPILE GHC dbDescription = Database.dbDescription #-}
{-# COMPILE GHC abort         = (\ _ -> Database.abort) #-}

-- Performs verification of a schema given that the input string
-- is a description of the database in the expected format.
performVerification : Schema → String → Bool
performVerification s x = P.verifyDbFormat s (toList x)

executeQuery : {s : Schema} → RA s → IO (Table s)
executeQuery {s} ra = runQuery (toSQL ra) >>= λ res →
                      return (P.parseSchema s (toList res))

-- This is the only exported function which can construct a handle.
connect : String → (s : Schema) → IO (Handle s)
connect table schema = dbDescription table >>= λ bs →
                         if performVerification schema bs
                         then return (handle schema table)
                         else abort
