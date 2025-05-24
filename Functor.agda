{-# OPTIONS --prop --rewriting #-}

module Functor where

open import Lib hiding (Maybe)

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
    
