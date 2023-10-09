module example where

open import Data.List.Base   using (List; []; _∷_; _++_; foldr)
open import Data.Product     using (_,_)
open import Data.String.Base using (String)
open import Data.Unit.Base   using (⊤)
open import Function.Base    using (_$_; _∘_)

open import DataTypes
open import RA

-- Schema for the cars table
Cars : Schema
Cars = ("pkey" , NAT)
     ∷ ("Model" , STR 20)
     ∷ ("Time" , STR 6)
     ∷ ("Wet"  , BOOL) ∷ []

-- Subset of the Cars schema that only has the Model column
Models : Schema
Models = ("Model" , STR 20) ∷ ("Time" , STR 6) ∷ []

-- Subset of the Cars schema that only has the Wet column
Wet : Schema
Wet = ("Wet" , BOOL) ∷ []

-- Generate the models schema from the cars schema
models : Handle Cars → RA Models
models h = Project Models (Read h)

-- Get the wet tests
wet : Handle Cars → RA Cars
wet h = Select (Cars ! "Wet") (Read h)

wetModels : Handle Cars → RA Models
wetModels h = Project Models (Select (Cars ! "Wet") (Read h))

-- This is a little inconvenient
mazda : String
mazda = "Mazda"

-- Take only Mazda cars
cool : Handle Cars → RA Cars
cool h = Select ((Cars ! "Model") := Lit mazda) (Read h)

fast : Handle Cars → RA Cars
fast h = Select ((Cars ! "Time") :< Lit "2:12.3") (Read h)

slow : Handle Cars → RA Models
slow h = Project Models (Diff (Read h) (fast h))

nonWet : Handle Cars → RA Cars
nonWet h = Diff (Read h) (wet h)

union : Handle Cars → RA Cars
union h = Union (fast h) (Diff (Read h) (fast h))

prod : Handle Cars → RA (Models ++ Wet)
prod h = Product (Project Models (Read h)) (Project Wet (Read h))

open import IO
-- open IO.List using () renaming (mapM′ to mapM') -- ⊤ vs. polymorphic ⊤

-- Other namings of mapM like function are taken by the list
-- library.
mapM' : {A B : Set} → (A → IO B) → List A → IO ⊤
mapM' f xs = foldr (λ a b → f a >> b) (return _) xs

-- How many cars do better than a given time
test1 : IO ⊤
test1 = do
  putStrLn "\n\nFast Cars"
  h ← lift $ connect "cars" Cars
  putStrLn (toSQL (fast h))
  res ← lift $ executeQuery (fast h)
  mapM' (putStrLn ∘ showRow) res

-- How long are the rows produced by the wet query
test2 : IO ⊤
test2 = do
  putStrLn "\n\nNon wet cars"
  h ← lift $ connect "cars" Cars
  putStrLn (toSQL (nonWet h))
  res ← lift $ executeQuery (nonWet h)
  mapM' (putStrLn ∘ showRow) res

-- Select the slow cars and display their models/times
test3 : IO ⊤
test3 = do
  putStrLn "\n\nSlow cars"
  h ← lift $ connect "cars" Cars
  putStrLn (toSQL (slow h))
  res ← lift $ executeQuery (slow h)
  mapM' (putStrLn ∘ showRow) res

test4 : IO ⊤
test4 = do
  putStrLn "\n\nUnion of fast and slow cars"
  h ← lift $ connect "cars" Cars
  putStrLn (toSQL (union h))
  res ← lift $ executeQuery (union h)
  mapM' (putStrLn ∘ showRow) res

test5 : IO ⊤
test5 = do
  putStrLn "\n\nProduct of Models with Wet"
  h ← lift $ connect "cars" Cars
  putStrLn (toSQL (prod h))
  res ← lift $ executeQuery (prod h)
  mapM' (putStrLn ∘ showRow) res

main : _
main = run $ test1 >> test2 >> test3 >> test4 >> test5
