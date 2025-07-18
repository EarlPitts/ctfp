{-# OPTIONS --prop --rewriting #-}

module Functor where

open import Lib hiding (Maybe)

id : {A : Set} → A → A
id x = x

module MaybeFunctor where
    -- Maybe data type definition
    data Maybe (A : Set) : Set where
        Just    : A → Maybe A
        Nothing : Maybe A

    -- Functor implementation for Maybe
    fmap : ∀ {a b : Set} → (a → b) → Maybe a → Maybe b
    fmap f (Just x)  = Just (f x)
    fmap _ Nothing   = Nothing

    -- Functor laws proofs
    fmap-id : ∀ {A : Set} → (ma : Maybe A) → fmap (λ x → x) ma ≡ ma
    fmap-id Nothing = refl
    fmap-id (Just x) = cong Just refl

    fmap-comp : ∀ {A B C : Set} → (f : B → C) → (g : A → B) → (ma : Maybe A) → fmap (f ∘ g) ma ≡ (fmap f ∘ fmap g) ma
    fmap-comp f g Nothing =
        fmap (f ∘ g) Nothing
            ≡≡
        Nothing
            ≡≡
        fmap f Nothing
            ≡≡
        fmap f (fmap g Nothing)
            ≡≡
        (fmap f ∘ fmap g) Nothing
            ∎
    fmap-comp f g (Just x) =
        fmap (f ∘ g) (Just x)
            ≡≡
        Just ((f ∘ g) x)
            ≡≡
        Just (f (g x))
            ≡≡
        Just (f (g x))
            ≡≡
        (fmap f (Just (g x)))
            ≡≡
        (fmap f (fmap g (Just x)))
            ≡≡
        (fmap f ∘ fmap g) (Just x)
            ∎

open import Agda.Builtin.List

module ListFunctor where

    fmap : ∀ {a b : Set} → (a → b) → List a → List b
    fmap f [] = []
    fmap f (x ∷ l) = f x ∷ fmap f l

    -- Functor laws proofs
    fmap-id : ∀ {A : Set} → (ma : List A) → fmap (λ x → x) ma ≡ ma
    fmap-id [] = refl
    fmap-id (x ∷ l) = cong (x ∷_) (fmap-id l)

    fmap-comp : ∀ {A B C : Set} → (f : B → C) → (g : A → B) → (ma : List A) → fmap (f ∘ g) ma ≡ (fmap f ∘ fmap g) ma
    fmap-comp f g [] = refl
    fmap-comp f g (x ∷ xs) = 
        fmap (f ∘ g) (x ∷ xs)
            ≡≡
        (f (g x)) ∷ (fmap (f ∘ g) xs)
            ≡⟨ cong (f (g x) ∷_ ) (fmap-comp f g xs) ⟩
        fmap f (fmap g (x ∷ xs))
            ≡≡
        (fmap f ∘ fmap g) (x ∷ xs)
            ∎
    

module ReaderFunctor where

    record Reader (R A : Set) : Set where
      constructor reader
      field
        runReader : R → A

    fmap : ∀ {r a b : Set} → (a → b) → Reader r a → Reader r b
    fmap f ra = reader (f ∘ (Reader.runReader ra))

    -- Functor laws proofs
    fmap-id : ∀ {R A : Set} → (ra : Reader R A) → fmap id ra ≡ id ra
    fmap-id ra = 
        fmap id ra
            ≡≡ -- def of fmap, id and reader
        reader ((λ x → x) ∘ (Reader.runReader ra))
            ≡≡ -- def of comp
        reader (λ x → (Reader.runReader ra) x)
            ≡≡ -- eta
        reader (Reader.runReader ra)
            ≡≡ -- eta?
        ra
            ≡≡ -- id def
        id ra
            ∎
    
    fmap-comp : ∀ {R A B C : Set} → (f : B → C) → (g : A → B) → (ra : Reader R A) → fmap (f ∘ g) ra ≡ (fmap f ∘ fmap g) ra
    fmap-comp f g ra = 
        fmap (f ∘ g) ra
            ≡≡ -- def of Reader
        fmap (f ∘ g) (reader (Reader.runReader ra))
            ≡≡ -- def of comp
        fmap (λ x → f (g x)) (reader (Reader.runReader ra))
            ≡≡ -- def of fmap
        reader ((λ x → f (g x)) ∘ Reader.runReader ra)
            ≡≡ -- def of comp
        reader (λ x → f (g ((Reader.runReader ra) x)))
            ≡≡ -- def of comp
        reader (f ∘ (g ∘ (Reader.runReader ra)))
            ≡≡ -- def of fmap
        fmap f (reader (g ∘ (Reader.runReader ra)))
            ≡≡ -- def of fmap
        fmap f (fmap g (reader (Reader.runReader ra)))
            ≡≡ -- β red
        (λ x → fmap f (fmap g x)) (reader (Reader.runReader ra))
            ≡≡ -- def of Reader
        (λ x → fmap f (fmap g x)) ra
            ≡≡ -- def of comp
        (fmap f ∘ fmap g) ra
            ∎

module PairProfunctor where

  data Pair (A B : Set): Set where
    P : A → B → Pair A B

  bimap : ∀ { A B C D : Set } → (A → C) → (B → D) → Pair A B → Pair C D
  bimap f g (P a b) = P (f a) (g b)

  first : ∀ { A B C : Set } → (A → C) → Pair A B → Pair C B
  first f = bimap f id

  second : ∀ { A B D : Set } → (B → D) → Pair A B → Pair A D
  second g = bimap id g

  bimap-id : ∀ {A B : Set} → (pab : Pair A B) → bimap id id pab ≡ pab
  bimap-id (P a b) =
        bimap id id (P a b)
    ≡≡ -- Def bimap
        P (id a) (id b)
    ≡≡ -- Def id
        P a b
    ∎

  bimap-cons : ∀ { A B C D : Set } → (f : A → C) → (g : B → D) → (pab : (Pair A B)) → bimap f g pab ≡ ((first f) ∘ (second g )) pab
  bimap-cons f g (P a b) =
    bimap f g (P a b)
        ≡≡ -- Def of bimap
    (P (f a) (g b))
        ≡≡ -- Def of bimap
    (bimap f id (P a (g b)))
        ≡≡ -- Def of bimap
    (bimap f id (bimap id g (P a b)))
        ≡≡ -- Def of second
    (bimap f id (second g (P a b)))
        ≡≡ -- Def of first
    (first f (second g (P a b)))
        ≡≡ -- Def of comp
    (first f ∘ second g) (P a b)
        ∎
  
  bimap-comp : ∀ { A B C D E F : Set } → (f : A → C) → (g : B → D) → (h : C → E) → (i : D → F) → (pab : Pair A B)
    → bimap (h ∘ f) (i ∘ g) pab ≡ (bimap h i ∘ bimap f g) pab
  bimap-comp f g h i (P a b) =
    bimap (h ∘ f) (i ∘ g) (P a b)
        ≡≡ -- Def of bimap
    (P ((h ∘ f) a) ((i ∘ g) b))
        ≡≡ -- Def of comp and eta
    (P (h (f a)) (i (g b)))
        ≡≡ -- Def of bimap
    bimap h i (P (f a) (g b))
        ≡≡ -- Def of bimap
    bimap h i (bimap f g (P a b))
        ≡≡ -- Eta
    (λ x → (bimap h i (bimap f g x))) (P a b)
        ≡≡ -- Def of comp
    (bimap h i ∘ bimap f g) (P a b)
        ∎


module Iso where

    data Maybe (A : Set) : Set where
        Just    : A → Maybe A
        Nothing : Maybe A

    data Either (A B : Set) : Set where
        Left  : A → Either A B
        Right : B → Either A B

    data Const (A B : Set) : Set where
      const : A → Const A B

    data Unit : Set where
      unit : Unit

    data Identity (A : Set) : Set where
      identity : A → Identity A

    iso-→ : ∀ {A : Set} → Maybe A → Either (Const Unit A) (Identity A)
    iso-→ (Just x) = Right (identity x)
    iso-→ Nothing = Left (const unit)

    iso-← : ∀ {A : Set} → Either (Const Unit A) (Identity A) → Maybe A
    iso-← (Left (const unit)) = Nothing
    iso-← (Right (identity a)) = Just a

    -- iso : ∀ {A : Set} → Maybe A ≡ Either (Const Unit A) (Identity A)
    -- iso = {! iso-→ ∧ iso-←!}
