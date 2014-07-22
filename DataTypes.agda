module DataTypes where

open import Data.Bool
open import Data.BoundedVec hiding (fromList ; _∷_ ; [])
open import Data.Char hiding (_==_)
open import Data.Empty using (⊥)
open import Data.List hiding (_++_)
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.String hiding (toList)
open import Data.Unit using (Unit)
open import Function using (_∘_)

import Data.Nat.Show as NS

-- Our mini universe of types
data U : Set where
  CHAR : U
  NAT  : U
  BOOL : U
  STR  : ℕ → U
  
-- The name of a type as it corresponds to its given SQL name.
typeName : U → String
typeName CHAR     = "CHAR"
typeName NAT      = "INTEGER"
typeName BOOL     = "Boolean"
typeName (STR x)  = "CHAR(" ++ NS.show x ++ ")"

-- Map the universe of SQL types to agda
-- equivalents.
-- Strings are a little odd in SQL in that they are
-- paramterized by a length, but the length serves only
-- as an upper bound on the number of characters present.
-- This behaviour is mimicked by the BoundedVec type.
el : U → Set
el CHAR     = Char
el NAT      = ℕ
el BOOL     = Bool
el (STR x)  = BoundedVec Char x

So : Bool → Set
So true  = Unit
So false = ⊥

-- An attribute corresponds to a column in the database.
-- It is a column name along with the SQL type.
Attribute : Set
Attribute = Σ String (λ _ → U)

Schema : Set
Schema = List Attribute

-- Does a column name exist in the schema?
occurs : String → Schema → Bool
occurs x []       = false
occurs x (( name , type ) ∷ s) with x == name
... | true  = true
... | false = occurs x s

-- Lookup the corresponding column type given a column name
-- in the schema.
lookup : (nm : String) → (s : Schema) → (p : So (occurs nm s)) → U
lookup nm [] ()
lookup nm ((name , type) ∷ ss) p with nm == name
... | true  = type
... | false = lookup nm ss p

-- This could be improved to ensure that the types
-- line up as well. That may prove necessarry later,
-- but may be tricky to implement.
sub : Schema → Schema → Bool
sub [] p      = true
sub (( name , type ) ∷ s) p with occurs name p
... | false = false
... | true  = sub s p

-- Possible alternative to using lookup? Encode
-- lookup as a data type and use that. Might make
-- certain operations more tricky.
_∉_ : String → Schema → Bool
x ∉ []      = true
x ∉ (( name , type ) ∷ s) with x == name
... | true  = false
... | false = x ∉ s

-- Ensures that a pair of schemas are disjoint.
-- This must be the case for when we want to take the
-- product of two schemas.
-- This should probably be used bidirectionally on schemas
disjoint : Schema → Schema → Bool
disjoint [] ys = true
disjoint (( name , _ ) ∷ xs) ys with name ∉ ys
... | false = false
... | true  = disjoint xs ys

-- A row from the database is a list with knowlege of the
-- database schema.
data Row : Schema → Set where
  EmptyRow : Row []
  ConsRow  : ∀ {s name} → {u : U} → el u → Row s → Row (( name , u ) ∷ s)

-- Convert a row to a list of element wise string representations.
-- This makes for a convenient way to display the rows.
rowToList : {s : Schema} → Row s → List String
rowToList {[]} EmptyRow = []
rowToList {( n , CHAR ) ∷ s} (ConsRow x xs)          = ("'" ++ fromList [ x ] ++ "'") ∷ rowToList xs
rowToList {( n , NAT ) ∷ s} (ConsRow x xs)           = NS.show x ∷ rowToList xs
rowToList {( n , BOOL ) ∷ s} (ConsRow true xs)       = "1" ∷ rowToList xs
rowToList {( n , BOOL ) ∷ s} (ConsRow false xs)      = "0" ∷ rowToList xs
rowToList {( n , STR x ) ∷ s} (ConsRow x₁ xs)        = ("\"" ++ fromList (toList x₁) ++ "\"") ∷ rowToList xs

-- Show a row 
showRow : {s : Schema} → Row s → String
showRow = foldr _++_ "" ∘ intersperse "|" ∘ rowToList

Table : Schema → Set
Table s = List (Row s)

-- The length of a row from the database. This is, perhaps, not that useful.
∥_∥ : ∀ {s} → Row s → ℕ
∥ EmptyRow ∥    = zero
∥ ConsRow x y ∥ = suc ∥ y ∥

