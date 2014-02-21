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
Imp'' Γ (AFun α₁ α₂) = ∀ {Γ'} → Γ ↝ Γ' → (Imp'' Γ' α₁ → Imp'' Γ' α₂)
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
lift2 (AFun x x₁) Γ↝Γ' v = λ Γ'↝Γ'' → v (↝-trans Γ↝Γ' Γ'↝Γ'')
lift2 (D x₁) Γ↝Γ' v = elevate (↝↝-base Γ↝Γ') v

lookup2 : ∀ {α Δ Γ Γ'} → Γ ↝ Γ' → AEnv2 Γ Δ → α ∈ Δ → Imp'' Γ' α
lookup2 Γ↝Γ' (consS p α v env) hd = lift2 α Γ↝Γ' v
lookup2 Γ↝Γ' (consS p α₁ v env) (tl x) = lookup2 (↝-trans p Γ↝Γ') env x
lookup2 Γ↝Γ' (consD α v env) hd = lift2 (D α) Γ↝Γ' v
lookup2 ↝-refl (consD α₁ v env) (tl x) = lookup2 (↝-extend ↝-refl) env x
lookup2 (↝-extend Γ↝Γ') (consD α₁ v env) (tl x) = lookup2 (lem α₁ _ _ _ Γ↝Γ') env x

pe2 : ∀ {α Δ Γ} → AExp Δ α → AEnv2 Γ Δ → Imp'' Γ α
pe2 (AVar x) env = lookup2 ↝-refl env x
pe2 (AInt x) env = x
pe2 (AAdd e₁ e₂) env = pe2 e₁ env + pe2 e₂ env
pe2 {AFun α₂ α₁} (ALam e) env = λ Γ↝Γ' → λ y → pe2 e (consS Γ↝Γ' α₂ y env)
pe2 (AApp e₁ e₂) env = ((pe2 e₁ env) ↝-refl) (pe2 e₂ env)
pe2 (DInt x) env = EInt x
pe2 (DAdd e e₁) env = EAdd (pe2 e env) (pe2 e₁ env)
pe2 {D (Fun σ₁ σ₂)} (DLam e) env = ELam (pe2 e (consD σ₁ (EVar hd) env))
                                                 -- ELam (pe2 (consS (↝-extend {τ = σ₁} ↝-refl) (D σ₁) (EVar hd) env)) works too;
                                                 -- it is probably a canonical solution, but I (Lu) do not see why...
pe2 (DApp e e₁) env = EApp (pe2 e env) (pe2 e₁ env)

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
                     ((ALam (DLam {α₂ = Int} (DAdd y z)))))

  ex-pe-term1 : pe2 term1 [] ≡ ELam (ELam (EVar hd))
  ex-pe-term1 = refl

  ex-pe-term2 : pe2 term2 [] ≡ ELam (ELam (EVar hd))
  ex-pe-term2 = refl

-- end of file