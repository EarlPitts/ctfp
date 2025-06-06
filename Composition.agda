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
        ≡≡ -- def of ∘
    (λ a → id (f a))
        ≡≡ -- def of id
    (λ a → f a)
        ≡≡ -- η-equality
    f
        ∎

∘-right-id : ∀ {A B : Set} → (f : A → B) → (f ∘ id) ≡ f
∘-right-id f =
    f ∘ id
        ≡≡ -- def of ∘
    (λ a → f (id a))
        ≡≡ -- def of id
    (λ a → f a)
        ≡≡ -- η-equality
    f
        ∎

∘-assoc : {A B C D : Set} → (f : A → B) → (g : B → C) → (h : C → D)
    → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
∘-assoc f g h = 
    (h ∘ (g ∘ f))
        ≡≡ -- def of ∘
    (λ c → h ((g ∘ f) c))
        ≡≡ -- def of ∘
    (λ c → h ((λ a → g (f a)) c))
        ≡≡
    (λ a → (λ b → (h (g b))) (f a))
        ≡≡ -- def of ∘
    (λ a → (h ∘ g) (f a))
        ≡≡ -- def of ∘
    (h ∘ g) ∘ f
        ∎

