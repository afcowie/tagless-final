-- Solution to type-preserving interpretation using fancier types
-- Shin-cheng Mu, 2008
-- http://www.iis.sinica.edu.tw/~scm/2008/typed-lambda-calculus-interprete/

-- Thanks to dependent types, lookup and lookupEnv have no pattern-match
-- failure
-- Thanks to the type function ⟦_⟧ᵀ and GADT Term, we don't need universal type
-- Term expresses all and _only_ well-typed terms in the object language

-- I have seen similar code, and the claim that dependent types are
-- really needed to express the type system of simply-typed lambda-calculus

module Term where

open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Vec

data TExp : Set where
   N : TExp
   _⇒_ : (σ : TExp) → (τ : TExp) → TExp

⟦_⟧ᵀ : TExp → Set
⟦ N ⟧ᵀ = ℕ 
⟦ σ ⇒ τ ⟧ᵀ = ⟦ σ ⟧ᵀ → ⟦ τ ⟧ᵀ 

Cxt : ℕ → Set
Cxt n = Vec TExp n

data Term {n : ℕ} (Γ : Cxt n) : TExp → Set where
   val : ∀{σ} → (v : ⟦ σ ⟧ᵀ) → Term Γ σ
   var : (i : Fin n) → Term Γ (lookup i Γ)
   _∔_ : (m : Term Γ N) → (n : Term Γ N) → Term Γ N
   _·_ : ∀{σ τ} → (f : Term Γ (σ ⇒ τ)) → (e : Term Γ σ) → Term Γ τ 
   ƛ : ∀ σ {τ} → (e : Term (σ ∷ Γ) τ) → Term Γ (σ ⇒ τ)

data Env : {n : ℕ} → Cxt n → Set where
  [] : Env []
  _∷_ : ∀{σ n}{Γ : Cxt n} → (v : ⟦ σ ⟧ᵀ) → (ρ : Env Γ) → Env (σ ∷ Γ)

lookupEnv : ∀ {n}{Γ} → (i : Fin n) → (ρ : Env Γ) → ⟦ lookup i Γ ⟧ᵀ
lookupEnv zero (v ∷ ρ) = v 
lookupEnv (suc i) (_ ∷ ρ) = lookupEnv i ρ 

⟦_⟧ : ∀{n}{Γ : Cxt n}{σ} → Term Γ σ → Env Γ → ⟦ σ ⟧ᵀ
⟦ val v ⟧ ρ = v 
⟦ var i ⟧ ρ = lookupEnv i ρ 
⟦ m ∔ n ⟧ ρ = ⟦ m ⟧ ρ + ⟦ n ⟧ ρ 
⟦ f · e ⟧ ρ = ⟦ f ⟧ ρ (⟦ e ⟧ ρ) 
⟦ ƛ σ e ⟧ ρ = λ x → ⟦ e ⟧ x ∷ ρ   



