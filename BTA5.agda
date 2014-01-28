module BTA5 where

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
data Exp'' (Γ : Ctx) : Type → Set where
  EVar : ∀ {τ} → τ ∈ Γ → Exp'' Γ τ
  EInt : ℕ → Exp'' Γ Int
  EAdd : Exp'' Γ Int → Exp'' Γ Int -> Exp'' Γ Int
  ELam : ∀ {τ τ'} → Exp'' (τ ∷ Γ) τ' → Exp'' Γ (Fun τ τ')
  EApp : ∀ {τ τ'} → Exp'' Γ (Fun τ τ')  → Exp'' Γ τ → Exp'' Γ τ'


data AExp (Δ : ACtx) : AType → Set where
  AVar : ∀ {α} → α ∈ Δ → AExp Δ α
  AInt : ℕ → AExp Δ AInt
  AAdd : AExp Δ AInt → AExp Δ AInt → AExp Δ AInt
  ALam : ∀ {α₁ α₂}   → AExp (α₂ ∷ Δ) α₁ → AExp Δ (AFun α₂ α₁)
  AApp : ∀ {α₁ α₂}   → AExp Δ (AFun α₂ α₁) → AExp Δ α₂ → AExp Δ α₁
  DInt : ℕ → AExp Δ (D Int)
  DAdd : AExp Δ (D Int) → AExp Δ (D Int) → AExp Δ (D Int)
  DLam : ∀ {α₁ α₂}   → AExp ((D α₂) ∷ Δ) (D α₁) → AExp Δ (D (Fun α₂ α₁))
  DApp : ∀ {α₁ α₂}   → AExp Δ (D (Fun α₂ α₁)) → AExp Δ (D α₂) → AExp Δ (D α₁)

-- -- index Γ = nesting level of dynamic definitions / dynamic environment
Imp'' : Ctx → AType → Set
Imp'' Γ (AInt) = ℕ
Imp'' Γ (AFun α₁ α₂) = ∀ Γ' → Γ ↝ Γ' → (Imp'' Γ' α₁ → Imp'' Γ' α₂)
Imp'' Γ (D σ) = Exp'' Γ σ


-- -- index = nesting level of dynamic definitions
data AEnv2 : Ctx → ACtx → Set where
  [] : AEnv2 [] []
  consS : ∀ {Γ Δ Γ'} → Γ ↝ Γ' → (α : AType) → Imp'' Γ' α → AEnv2 Γ Δ → AEnv2 Γ' (α ∷ Δ)
  consD : ∀ {Γ Δ} → (σ : Type) → Exp'' (σ ∷ Γ)  σ → AEnv2 Γ Δ → AEnv2 (σ ∷ Γ) (D σ ∷ Δ) 



elevate-var : ∀ {Γ Γ' τ} → Γ ↝ Γ' → τ ∈ Γ → τ ∈ Γ'
elevate-var ↝-refl x = x
elevate-var (↝-extend Γ↝Γ') x = tl (elevate-var Γ↝Γ' x)

elevate-var2 : ∀ {Γ Γ' Γ'' τ} → Γ ↝ Γ' ↝ Γ'' → τ ∈ Γ → τ ∈ Γ''
elevate-var2 (↝↝-base x) x₁ = elevate-var x x₁
elevate-var2 (↝↝-extend Γ↝Γ'↝Γ'') hd = hd
elevate-var2 (↝↝-extend Γ↝Γ'↝Γ'') (tl x) = tl (elevate-var2 Γ↝Γ'↝Γ'' x)

elevate : ∀ {Γ Γ' Γ'' τ} → Γ ↝ Γ' ↝ Γ'' → Exp'' Γ τ → Exp'' Γ'' τ
elevate Γ↝Γ'↝Γ'' (EVar x) = EVar (elevate-var2 Γ↝Γ'↝Γ'' x)
elevate Γ↝Γ'↝Γ'' (EInt x) = EInt x
elevate Γ↝Γ'↝Γ'' (EAdd e e₁) = EAdd (elevate Γ↝Γ'↝Γ'' e) (elevate Γ↝Γ'↝Γ'' e₁)
elevate Γ↝Γ'↝Γ'' (ELam e) = ELam (elevate (↝↝-extend Γ↝Γ'↝Γ'') e)
elevate Γ↝Γ'↝Γ'' (EApp e e₁) = EApp (elevate Γ↝Γ'↝Γ'' e) (elevate Γ↝Γ'↝Γ'' e₁)

lift2 : ∀ {Γ Γ'} α → Γ ↝ Γ' → Imp'' Γ α → Imp'' Γ' α 
lift2 AInt p v = v
lift2 (AFun x x₁) Γ↝Γ' v = λ Γ'' Γ'↝Γ'' → v Γ'' (↝-trans Γ↝Γ' Γ'↝Γ'')
lift2 (D x₁) Γ↝Γ' v = elevate (↝↝-base Γ↝Γ') v

lookup2 : ∀ {α Δ Γ Γ'} → Γ ↝ Γ' → AEnv2 Γ Δ → α ∈ Δ → Imp'' Γ' α
lookup2 Γ↝Γ' (consS p α v env) hd = lift2 α Γ↝Γ' v
lookup2 Γ↝Γ' (consS p α₁ v env) (tl x) = lookup2 (↝-trans p Γ↝Γ') env x
lookup2 Γ↝Γ' (consD α v env) hd = lift2 (D α) Γ↝Γ' v
lookup2 ↝-refl (consD α₁ v env) (tl x) = lookup2 (↝-extend ↝-refl) env x
lookup2 (↝-extend Γ↝Γ') (consD α₁ v env) (tl x) = lookup2 (lem α₁ _ _ _ Γ↝Γ') env x

pe2 : ∀ {α Δ} Γ → AExp Δ α → AEnv2 Γ Δ → Imp'' Γ α
pe2 Γ (AVar x) env = lookup2 ↝-refl env x
pe2 Γ (AInt x) env = x
pe2 Γ (AAdd e₁ e₂) env = pe2 Γ e₁ env + pe2 Γ e₂ env
pe2 {AFun α₂ α₁} Γ  (ALam e) env = λ Γ' Γ↝Γ' → λ y → pe2 Γ' e (consS Γ↝Γ' α₂ y env)
pe2 Γ (AApp e₁ e₂) env = pe2 Γ e₁ env Γ ↝-refl (pe2 Γ e₂ env)
pe2 Γ (DInt x) env = EInt x
pe2 Γ (DAdd e e₁) env = EAdd (pe2 Γ e env) (pe2 Γ e₁ env)
pe2 {D (Fun σ₁ σ₂)}Γ (DLam e) env = ELam (pe2 (σ₁ ∷ Γ) e (consD σ₁ (EVar hd) env))
pe2 Γ (DApp e e₁) env = EApp (pe2 Γ e env) (pe2 Γ e₁ env)
-- pe2 Γ (AVar x) env = lookup2 ↝-refl env x
-- pe2 Γ (AInt S x) env = x
-- pe2 Γ (AInt D x) env = EInt x
-- pe2 Γ (AAdd S e₁ e₂) env = pe2 Γ e₁ env + pe2 Γ e₂ env
-- pe2 Γ (AAdd D e₁ e₂) env = EAdd (pe2 Γ e₁ env) (pe2 Γ e₂ env)
-- pe2 {Ann S (SFun α₂ α₁)} Γ (ALam .S w e) env = λ Γ' Γ↝Γ' → λ y → pe2 {α₁} Γ' e (consS Γ↝Γ' α₂ y env)
-- pe2 Γ (ALam {α₂} {α₁} D (wf-fun w₁ w₂ d≤bt₁ d≤bt₂) e) env 
--   with lem-IsDynamic-by-wf α₁ d≤bt₁ | lem-IsDynamic-by-wf α₂ d≤bt₂ 
-- pe2 Γ (ALam {.(Ann D σ₂)} {.(Ann D σ₁)} D (wf-fun _ _ d≤bt₁ d≤bt₂) e) env
--   | is-dyn σ₁ | is-dyn σ₂ = ELam (pe2 (erase (Ann D σ₁) ∷ Γ) e (consD (Ann D σ₁) d≤bt₁ (EVar hd) env))
-- pe2 Γ (AApp S w e₁ e₂) env = pe2 Γ e₁ env Γ ↝-refl (pe2 Γ e₂ env)
-- pe2 Γ (AApp {α₂} {α₁} D (wf-fun w₁ w₂ d≤bt₁ d≤bt₂) e e₁) env 
--   with lem-IsDynamic-by-wf α₁ d≤bt₁ | lem-IsDynamic-by-wf α₂ d≤bt₂ 
-- pe2 Γ (AApp {.(Ann D σ₂)} {.(Ann D σ₁)} D (wf-fun w₁ w₂ d≤bt₁ d≤bt₂) e e₁) env
--   | is-dyn σ₁ | is-dyn σ₂ = EApp (pe2 Γ e env) (pe2 Γ e₁ env)

