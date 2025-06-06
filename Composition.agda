{-# OPTIONS --prop --rewriting #-}

module Composition where

open import Lib hiding (_∘_)

id : {A : Set} → A → A
id x = x

_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
_∘_ f g = λ a → f (g a)

∘-left-id : ∀ {A B : Set} → (f : A → B) → (id ∘ f) ≡ f
∘-left-id f =
    id ∘ f
        ≡≡ -- def of comp
    (λ a → id (f a))
        ≡≡ -- def of id
    (λ a → f a)
        ≡≡ -- η-equality
    f
        ∎

∘-right-id : ∀ {A B : Set} → (f : A → B) → (f ∘ id) ≡ f
∘-right-id f =
    f ∘ id
        ≡≡ -- def of comp
    (λ a → f (id a))
        ≡≡ -- def of id
    (λ a → f a)
        ≡≡ -- η-equality
    f
        ∎
