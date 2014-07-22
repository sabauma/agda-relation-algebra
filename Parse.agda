module Parse where

open import Data.Bool
open import Data.BoundedVec hiding (toList) renaming ([] to ⟨⟩ ; _∷_ to _::_)
open import Data.Char using (Char ; _==_ ; toNat)
open import Data.Empty
open import Data.List using (any ; List ; foldl ; foldr ; span ; length ; _∷_ ; [])
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.String using (String ; toList ; _++_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_])
open import Data.Unit using (⊤ ; tt)
open import Function using (_∘_ ; const)

open import DataTypes

mutual

    data Format : Set where
      Bad     : Format
      End     : Format
      Base    : U → Format
      Plus    : Format → Format → Format
      SkipL   : Format → Format → Format
      SkipR   : Format → Format → Format
      Bounded : ℕ → Format → Format
      Many    : Format → Format
      SepBy   : Format → Format → Format
      Read    : (f : Format) → (⟦ f ⟧ → Format) → Format

    ⟦_⟧ : Format → Set
    ⟦ Bad ⟧         = ⊥
    ⟦ End ⟧         = ⊤
    ⟦ Base u ⟧      = el u
    ⟦ Plus f₁ f₂ ⟧  = ⟦ f₁ ⟧ ⊎ ⟦ f₂ ⟧
    ⟦ SkipL f₁ f₂ ⟧ = ⟦ f₂ ⟧
    ⟦ SkipR f₁ f₂ ⟧ = ⟦ f₁ ⟧
    ⟦ Bounded n f ⟧ = BoundedVec ⟦ f ⟧ n
    ⟦ Many f ⟧      = List ⟦ f ⟧
    ⟦ SepBy f s ⟧   = List ⟦ f ⟧
    ⟦ Read f₁ f₂ ⟧  = Σ ⟦ f₁ ⟧ (λ x → ⟦ f₂ x ⟧)

infixl 1 _⋙_
infixl 1 _>>_
infixl 1 _<<_

_⋙_ : Format → Format → Format
_⋙_ = SepBy

_>>_ : Format → Format → Format
_>>_ = SkipL

_<<_ : Format → Format → Format
_<<_ = SkipR

_>>=_ : (f : Format) → (⟦ f ⟧ → Format) → Format
_>>=_ = Read

_⊕_ : Format → Format → Format
_⊕_ = Plus

satisfy : (f : Format) → (⟦ f ⟧ → Bool) → Format
satisfy f p = f >>= (λ x → if p x then End else Bad)

char : Char → Format
char c = satisfy (Base CHAR) (_==_ c)

specialChars : List Char
specialChars = '\"' ∷ '\\' ∷ []

member : List Char → Char → Bool
member xs c = any (λ x → x == c) xs

escaped : Format
escaped = char '\\' >> satisfy (Base CHAR) (member specialChars)

sqlChar : Format
sqlChar = escaped ⊕ satisfy (Base CHAR) (not ∘ member specialChars)

-- Description of a parser that will consume the string given
-- to it. It will produce no result; it is only good for checking
-- that a parse of the string is possible.
eatString : String → Format
eatString = foldr (λ a acc → char a >> acc) End ∘ toList

-- How should each of the base formats be parsed, given that they
-- are SQL data types.
baseFormat : U → Format
baseFormat CHAR    = Base CHAR --satisfy (Base CHAR) (λ x → not (x == '\"'))
baseFormat (STR n) = char '\"' >> (Bounded n sqlChar) << char '\"'
baseFormat x       = Base x

-- Convert a schema to the format that parses that schema.
schemaToFormat : Schema → Format
schemaToFormat []             = End
schemaToFormat ((x , t) ∷ []) = baseFormat t
schemaToFormat ((x , t) ∷ s)  = baseFormat t >>= (λ x → char '|' >> (schemaToFormat s))

chompRest : Format
chompRest = Many (satisfy (Base CHAR) (λ x → not (x == '\n')))

-- How to parse the null flag on the DB specification.
-- SQLite stores this as "Not null" rather than null, so
-- this flips the bit.
nullFlag : U → Format
nullFlag _ = char '0' ⊕ char '1'

-- Convert a schema into the parser that will parse the description
-- of the given table.
schemaToDbFormat : Schema → Format
schemaToDbFormat []                   = End
schemaToDbFormat ((name , type) ∷ []) = Base NAT >> char '|'
                                      >> char '\"' >> eatString name >> char '\"' >> char '|'
                                      >> eatString ("\"" ++ typeName type ++ "\"") >> char '|'
                                      >> chompRest
schemaToDbFormat ((name , type) ∷ xs) = Base NAT >> char '|'
                                      >> char '\"' >> eatString name >> char '\"' >> char '|'
                                      >> eatString ("\"" ++ typeName type ++ "\"") >> char '|'
                                      >> chompRest >> char '\n'
                                      >> schemaToDbFormat xs

-- The first row for the described database format is going to
-- include the primary key, which we care nothing about at this
-- point.
--schemaToDbFormat : Schema → Format
--schemaToDbFormat x = chompRest >> schemaToDbFormat′ x

isNumber : Char → Bool
isNumber '0' = true
isNumber '1' = true
isNumber '2' = true
isNumber '3' = true
isNumber '4' = true
isNumber '5' = true
isNumber '6' = true
isNumber '7' = true
isNumber '8' = true
isNumber '9' = true
isNumber _   = false

addChar : ℕ → Char → ℕ
addChar n c = 10 * n + (toNat c ∸ toNat '0')

makeℕ : List Char → ℕ
makeℕ = foldl addChar 0

-- The type returned by the parser. The parser can fail, or
-- it can produce a pair consisting of the specified type along
-- with the remaining character stream.
ParseResult : Set → Set
ParseResult s = Maybe (Σ s (λ x → List Char))

-- Greedily consume numbers in the input stream and
-- convert the result to a number
readℕ : List Char → ParseResult ℕ
readℕ xs with span isNumber xs
... | ( [] , zs ) = nothing
... | ( ys , zs ) = just (makeℕ ys , zs )

mutual

    readStr : (n : ℕ) → List Char → ParseResult (BoundedVec Char n)
    readStr zero xs          = just (⟨⟩ , xs)
    readStr (suc n) []       = just (⟨⟩ , [])
    readStr (suc n) (x ∷ xs) with readStr n xs
    ... | nothing       = just (x :: ⟨⟩ , xs)
    ... | just (y , ys) = just (x :: y  , ys)

    read : (u : U) → List Char → ParseResult (el u)
    read CHAR []          = nothing
    read CHAR (x ∷ xs)    = just (x , xs)
    read NAT bs           = readℕ bs
    read BOOL ('0' ∷ xs)  = just (false , xs)
    read BOOL ('1' ∷ xs)  = just (true , xs)
    read BOOL xs          = nothing
    read (STR n) xs       = readStr n xs

mutual

    parseMany : (f : Format) → ℕ → List Char → ParseResult (List ⟦ f ⟧)
    parseMany f zero as    = nothing
    parseMany f (suc n) [] = just ([] , [])
    parseMany f (suc n) as with parse f as
    ... | nothing          = just ([] , as)
    ... | just (x , bs) with parseMany f n bs
    ... | nothing          = just (x ∷ [] , bs)
    ... | just (y , cs)    = just (x ∷ y  , cs)

    parseBounded : (f : Format) → (n : ℕ) → List Char → Maybe (Σ (BoundedVec ⟦ f ⟧ n) (λ x → List Char))
    parseBounded f 0 xs     = just (⟨⟩ , xs)
    parseBounded f (suc n) xs with parse f xs
    ... | nothing           = just (⟨⟩ , xs)
    ... | just (v , rest) with parseBounded f n rest
    ... | nothing           = just (v :: ⟨⟩ , rest)
    ... | just (v′ , rest′) = just (v :: v′ , rest′)

    -- Parse a given format separated by another format.
    parseSepBy : (f : Format) → (s : Format) → ℕ → List Char 
               → ParseResult (List ⟦ f ⟧)
    parseSepBy f s zero as    = nothing
    parseSepBy f s (suc n) [] = just ([] , [])
    parseSepBy f s (suc n) as with parse f as
    ... | nothing          = just ([] , as)
    ... | just (x , bs) with parse s bs
    ... | nothing          = just (x ∷ [] , bs)
    ... | just (_ , cs) with parseSepBy f s n cs
    ... | nothing          = nothing -- Must provide more if we parsed the separator
    ... | just (ys , ds)   = just (x ∷ ys , ds)

    parse : (f : Format) → List Char → ParseResult ⟦ f ⟧
    parse Bad bs          = nothing
    parse End bs          = just (tt , bs)
    parse (Base u) bs     = read u bs
    parse (Plus f₁ f₂) bs with parse f₁ bs
    ... | just (x , cs)   = just (inj₁ x , cs)
    ... | nothing with parse f₂ bs
    ... | just (y , ds)   = just (inj₂ y , ds)
    ... | nothing         = nothing
    parse (SkipL f₁ f₂) bs with parse f₁ bs
    ... | nothing         = nothing
    ... | just (x , cs)   = parse f₂ cs
    parse (SkipR f₁ f₂) bs with parse f₁ bs
    ... | nothing         = nothing
    ... | just (x , cs) with parse f₂ cs
    ... | nothing         = nothing
    ... | just (y , ds)   = just (x , ds)
    parse (Bounded n f) bs = parseBounded f n bs
    parse (Many f) bs     = parseMany f (length bs) bs
    parse (SepBy f s) bs  = parseSepBy f s (length bs) bs
    parse (Read f₁ f₂) bs with parse f₁ bs
    ... | nothing         = nothing
    ... | just (x , cs) with parse (f₂ x) cs
    ... | nothing         = nothing
    ... | just (y , ds)   = just ((x , y) , ds)

-- Map over BoundVectors. This is needed to make some of the parsing
-- over strings go through.
mapBV : ∀ {A B n} → (A → B) → BoundedVec A n → BoundedVec B n
mapBV f x with view x
... | []v     = ⟨⟩
... | y ∷v ys = f y :: mapBV f ys

-- Use a schema to unpack parsed data into the corresponding Row type.
-- This shows that the parser generates the expected data type from the
-- given format.
unravelSchema : (s : Schema) → ⟦ schemaToFormat s ⟧ → Row s
unravelSchema [] v = EmptyRow
unravelSchema (( name , CHAR ) ∷ []) v            = ConsRow v EmptyRow
unravelSchema (( name , NAT ) ∷ []) v             = ConsRow v EmptyRow
unravelSchema (( name , BOOL ) ∷ []) v            = ConsRow v EmptyRow
unravelSchema (( name , STR _ ) ∷ []) v           = ConsRow (mapBV [ proj₁ , proj₁ ] v) EmptyRow
unravelSchema (( name , CHAR ) ∷ x ∷ s) (l , r)   = ConsRow l (unravelSchema (x ∷ s) r)
unravelSchema (( name , NAT ) ∷ x ∷ s) (l , r)    = ConsRow l (unravelSchema (x ∷ s) r)
unravelSchema (( name , BOOL ) ∷ x ∷ s) (l , r)   = ConsRow l (unravelSchema (x ∷ s) r)
unravelSchema (( name , STR _ ) ∷ x ∷ s) (l , r)  = ConsRow (mapBV [ proj₁ , proj₁ ] l) (unravelSchema (x ∷ s) r)

-- Parse a list of characters from the format specified by the given
-- schema. This is expected to consume all of the input.
parseSchema : (s : Schema) → List Char → Table s
parseSchema s bs with parse (schemaToFormat s ⋙ char '\n') bs
... | just (v , []) = Data.List.map (unravelSchema s) v
... | _             = []

-- Perform verification of the database format.
verifyDbFormat : (s : Schema) → List Char → Bool
verifyDbFormat s bs with parse (schemaToDbFormat s) bs
... | just (v , xs) = true
... | _             = false
