-- This version is a little simpler. AEnv is now defined for any Γ.
module BTA6 where

open import Data.Nat hiding (_<_)
open import Data.Bool
open import Data.List

open import Data.Nat.Properties

open import Relation.Nullary

-----------------
-- CLEANUP (∈) : this is surely in the standard library
-----------------
-- More general purpose definitions (should also be in standard library)
-- list membership
infix 4 _∈_
data _∈_ {A : Set} : A → List A → Set where
  hd : ∀ {x xs} → x ∈ (x ∷ xs)
  tl : ∀ {x y xs} → x ∈ xs → x ∈ (y ∷ xs)


data Type : Set where
  Int : Type
  Fun : Type → Type → Type


data AType : Set where
    AInt  : AType
    AFun  : AType → AType → AType
    D     : Type → AType

-- typed annotated expressions
ACtx = List AType



Ctx = List Type

-----------------------
-- CLEANUP (≤) : these properties are surely in the standard library
-----------------------
≤-refl : ∀ {n} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

-----------------------
-- CLEANUP (≤) : these properties are surely in the standard library
-----------------------
≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
≤-trans z≤n q = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

-----------------------
-- CLEANUP (≤) : these properties are surely in the standard library
-----------------------
≤-suc-right : ∀ {m n} → m ≤ n → m ≤ suc n
≤-suc-right z≤n = z≤n
≤-suc-right (s≤s p) = s≤s (≤-suc-right p)

-----------------------
-- CLEANUP (≤) : these properties are surely in the standard library
-----------------------
≤-suc-left : ∀ {m n} → suc m ≤ n → m ≤ n
≤-suc-left (s≤s p) = ≤-suc-right p

data _↝_ : Ctx → Ctx → Set where
  ↝-refl   : ∀ {Γ}      → Γ ↝ Γ
  ↝-extend : ∀ {Γ Γ' τ} → Γ ↝ Γ' → Γ ↝ (τ ∷ Γ')

↝-≤ : ∀ Γ Γ' → Γ ↝ Γ' → length Γ ≤ length Γ'
↝-≤ .Γ' Γ' ↝-refl = ≤-refl
↝-≤ Γ .(τ ∷ Γ') (↝-extend {.Γ} {Γ'} {τ} Γ↝Γ') = ≤-suc-right (↝-≤ Γ Γ' Γ↝Γ')

↝-no-left : ∀ Γ τ → ¬ (τ ∷ Γ) ↝ Γ
↝-no-left Γ τ p = 1+n≰n (↝-≤ (τ ∷ Γ) Γ p)

↝-trans : ∀ {Γ Γ' Γ''} → Γ ↝ Γ' → Γ' ↝ Γ'' → Γ ↝ Γ''
↝-trans Γ↝Γ' ↝-refl = Γ↝Γ'
↝-trans Γ↝Γ' (↝-extend Γ'↝Γ'') = ↝-extend (↝-trans Γ↝Γ' Γ'↝Γ'')

lem : ∀ x y xs xs' → (x ∷ xs) ↝ xs' → xs ↝ (y ∷ xs')
lem x y xs .(x ∷ xs) ↝-refl = ↝-extend (↝-extend ↝-refl)
lem x y xs .(x' ∷ xs') (↝-extend {.(x ∷ xs)} {xs'} {x'} p) = ↝-extend (lem x x' xs xs' p)


data _↝_↝_ : Ctx → Ctx → Ctx → Set where
  ↝↝-base   : ∀ {Γ Γ''} → Γ ↝ Γ'' → Γ ↝ [] ↝ Γ''
  ↝↝-extend : ∀ {Γ Γ' Γ'' τ} → Γ ↝ Γ' ↝ Γ'' → (τ ∷ Γ) ↝ (τ ∷ Γ') ↝ (τ ∷ Γ'')

-- Typed residula expressions
data Exp (Γ : Ctx) : Type → Set where
  EVar : ∀ {τ} → τ ∈ Γ → Exp Γ τ
  EInt : ℕ → Exp Γ Int
  EAdd : Exp Γ Int → Exp Γ Int -> Exp Γ Int
  ELam : ∀ {τ τ'} → Exp (τ ∷ Γ) τ' → Exp Γ (Fun τ τ')
  EApp : ∀ {τ τ'} → Exp Γ (Fun τ τ')  → Exp Γ τ → Exp Γ τ'

module Exp-Eval where
  -- interpretation of Exp types
  EImp : Type → Set
  EImp Int = ℕ
  EImp (Fun τ₁ τ₂) = EImp τ₁ → EImp τ₂

  -- Exp environments
  data Env : Ctx → Set where 
    [] : Env []
    _∷_ : ∀ {τ Γ} → EImp τ → Env Γ → Env (τ ∷ Γ)
  
  lookupE : ∀ { τ Γ } → τ ∈ Γ → Env Γ → EImp τ
  lookupE hd (x ∷ env) = x
  lookupE (tl v) (x ∷ env) = lookupE v env

  -- evaluation of Exp
  ev : ∀ {τ Γ} → Exp Γ τ → Env Γ → EImp τ
  ev (EVar x) env = lookupE x env
  ev (EInt x) env = x
  ev (EAdd e f) env = ev e env + ev f env
  ev (ELam e) env = λ x → ev e (x ∷ env)
  ev (EApp e f) env = ev e env (ev f env)



data AExp (Δ : ACtx) : AType → Set where
  AVar : ∀ {α} → α ∈ Δ → AExp Δ α
  AInt : ℕ → AExp Δ AInt
  AAdd : AExp Δ AInt → AExp Δ AInt → AExp Δ AInt
  ALam : ∀ {α₁ α₂}   → AExp (α₁ ∷ Δ) α₂ → AExp Δ (AFun α₁ α₂)
  AApp : ∀ {α₁ α₂}   → AExp Δ (AFun α₂ α₁) → AExp Δ α₂ → AExp Δ α₁
  DInt : ℕ → AExp Δ (D Int)
  DAdd : AExp Δ (D Int) → AExp Δ (D Int) → AExp Δ (D Int)
  DLam : ∀ {σ₁ σ₂}   → AExp ((D σ₁) ∷ Δ) (D σ₂) → AExp Δ (D (Fun σ₁ σ₂))
  DApp : ∀ {α₁ α₂}   → AExp Δ (D (Fun α₂ α₁)) → AExp Δ (D α₂) → AExp Δ (D α₁)

-- -- index Γ = nesting level of dynamic definitions / dynamic environment
Imp : Ctx → AType → Set
Imp Γ (AInt) = ℕ
Imp Γ (AFun α₁ α₂) = ∀ {Γ'} → Γ ↝ Γ' → (Imp Γ' α₁ → Imp Γ' α₂)
Imp Γ (D σ) = Exp Γ σ


elevate-var : ∀ {Γ Γ' τ} → Γ ↝ Γ' → τ ∈ Γ → τ ∈ Γ'
elevate-var ↝-refl x = x
elevate-var (↝-extend Γ↝Γ') x = tl (elevate-var Γ↝Γ' x)

elevate-var2 : ∀ {Γ Γ' Γ'' τ} → Γ ↝ Γ' ↝ Γ'' → τ ∈ Γ → τ ∈ Γ''
elevate-var2 (↝↝-base x) x₁ = elevate-var x x₁
elevate-var2 (↝↝-extend Γ↝Γ'↝Γ'') hd = hd
elevate-var2 (↝↝-extend Γ↝Γ'↝Γ'') (tl x) = tl (elevate-var2 Γ↝Γ'↝Γ'' x)

elevate : ∀ {Γ Γ' Γ'' τ} → Γ ↝ Γ' ↝ Γ'' → Exp Γ τ → Exp Γ'' τ
elevate Γ↝Γ'↝Γ'' (EVar x) = EVar (elevate-var2 Γ↝Γ'↝Γ'' x)
elevate Γ↝Γ'↝Γ'' (EInt x) = EInt x
elevate Γ↝Γ'↝Γ'' (EAdd e e₁) = EAdd (elevate Γ↝Γ'↝Γ'' e) (elevate Γ↝Γ'↝Γ'' e₁)
elevate Γ↝Γ'↝Γ'' (ELam e) = ELam (elevate (↝↝-extend Γ↝Γ'↝Γ'') e)
elevate Γ↝Γ'↝Γ'' (EApp e e₁) = EApp (elevate Γ↝Γ'↝Γ'' e) (elevate Γ↝Γ'↝Γ'' e₁)

lift : ∀ {Γ Γ'} α → Γ ↝ Γ' → Imp Γ α → Imp Γ' α 
lift AInt p v = v
lift (AFun x x₁) Γ↝Γ' v = λ Γ'↝Γ'' → v (↝-trans Γ↝Γ' Γ'↝Γ'')
lift (D x₁) Γ↝Γ' v = elevate (↝↝-base Γ↝Γ') v

-- A little weaker, but much simpler
data AEnv (Γ : Ctx) : ACtx → Set where
  [] : AEnv Γ []
  cons : ∀ {Δ} (α : AType) → Imp Γ α → AEnv Γ Δ → AEnv Γ (α ∷ Δ)

lookup : ∀ {α Δ Γ} → AEnv Γ Δ → α ∈ Δ → Imp Γ α
lookup (cons α v env) hd =  v 
lookup (cons α₁ v env) (tl x) = lookup env x

liftEnv : ∀ {Γ Γ' Δ} → Γ ↝ Γ' → AEnv Γ Δ → AEnv Γ' Δ
liftEnv Γ↝Γ' [] = []
liftEnv Γ↝Γ' (cons α x env) = cons α (lift α Γ↝Γ' x) (liftEnv Γ↝Γ' env)

consD : ∀ {Γ Δ} σ → AEnv Γ Δ → AEnv (σ ∷ Γ) (D σ ∷ Δ)
consD σ env = (cons (D σ) (EVar hd) (liftEnv (↝-extend {τ = σ} ↝-refl) env))

pe : ∀ {α Δ Γ} → AExp Δ α → AEnv Γ Δ → Imp Γ α
pe (AVar x) env = lookup env x 
pe (AInt x) env = x
pe (AAdd e₁ e₂) env = pe e₁ env + pe e₂ env
pe (ALam {α} e) env = λ Γ↝Γ' → λ y → pe e (cons α y (liftEnv Γ↝Γ' env)) 
pe (AApp e₁ e₂) env = ((pe e₁ env) ↝-refl) (pe e₂ env)
pe (DInt x) env = EInt x
pe (DAdd e e₁) env = EAdd (pe e env) (pe e₁ env)
pe (DLam {σ} e) env = ELam (pe e (consD σ env))
pe (DApp e e₁) env = EApp (pe e env) (pe e₁ env)


module Examples where
  open import Relation.Binary.PropositionalEquality

  x : ∀ {α Δ} → AExp (α ∷ Δ) α
  x = AVar hd
  y : ∀ {α₁ α Δ} → AExp (α₁ ∷ α ∷ Δ) α
  y = AVar (tl hd)
  z : ∀ {α₁ α₂ α Δ} → AExp (α₁ ∷ α₂ ∷ α ∷ Δ) α
  z = AVar (tl (tl hd))

-- Dλ y → let f = λ x → x D+ y in Dλ z → f z
  term1 : AExp [] (D (Fun Int (Fun Int Int)))
  term1 = DLam (AApp (ALam (DLam (AApp (ALam y) x)))
                     ((ALam (DAdd x y))))

-- Dλ y → let f = λ x → (Dλ w → x D+ y) in Dλ z → f z
-- Dλ y → (λ f → Dλ z → f z) (λ x → (Dλ w → x D+ y))
  term2 : AExp [] (D (Fun Int (Fun Int Int)))
  term2 = DLam (AApp (ALam (DLam (AApp (ALam y) x)))
                     ((ALam (DLam {σ₁ = Int} (DAdd y z)))))

  -- closed pe. In contrast to BTA5, it is now not clear what Γ is
  -- given an expression. So perhaps AEnv has it's merrits after all?
  pe[] : ∀ {α} → AExp [] α → Imp [] α
  pe[] e = pe e []

  ex-pe-term1 : pe[] term1 ≡ ELam (ELam (EVar hd))
  ex-pe-term1 = refl

  ex-pe-term2 : pe[] term2 ≡ ELam (ELam (EVar hd))
  ex-pe-term2 = refl

module Correctness where
  open Exp-Eval

  -- 1-1 mapping from AExp into Exp
  stripATy : AType → Type
  stripATy AInt = Int
  stripATy (AFun α₁ α₂) = Fun (stripATy α₁) (stripATy α₂)
  stripATy (D x) = x

  stripCx : ACtx → Ctx
  stripCx = map stripATy

  lem-strip-lookup : ∀ { α Δ} → α ∈ Δ → stripATy α ∈ stripCx Δ
  lem-strip-lookup hd = hd
  lem-strip-lookup (tl x) = tl (lem-strip-lookup x)

  strip : ∀ {α Δ} → AExp Δ α → Exp (stripCx Δ) (stripATy α)
  strip (AVar x) = EVar (lem-strip-lookup x)
  strip (AInt x) = EInt x
  strip (AAdd e f) = EAdd (strip e) (strip f)
  strip (ALam e) = ELam (strip e)
  strip (AApp e f) = EApp (strip e) (strip f)
  strip (DInt x) = EInt x
  strip (DAdd e f) = EAdd (strip e) (strip f)
  strip (DLam e) = ELam (strip e)
  strip (DApp e f) = EApp (strip e) (strip f)
  
  -- Now for the proof...
  module Proof where
    open import Relation.Binary.PropositionalEquality
    postulate ext : ∀ {τ₁ τ₂} {f g : EImp τ₁ → EImp τ₂} → (∀ x → f x ≡ g x) → f ≡ g

    -- pe-correct : ∀ { α Δ } → (e : AExp Δ α) → (env : AEnv Δ)
    --              → eval (pe e env)



module Precise-AEnv where

  data AEnv' : Ctx → ACtx → Set where
    [] : AEnv' [] []
    consS' : ∀ { Γ Γ' Δ } (α : AType) → Γ ↝ Γ' → Imp Γ' α → AEnv' Γ Δ → AEnv' Γ' (α ∷ Δ)
    consD' : ∀ { Γ Δ } (σ : Type) → Exp Γ σ → AEnv' Γ Δ → AEnv' (σ ∷ Γ) (D σ ∷ Δ)

