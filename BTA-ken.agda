module BTA-ken where
-- specialize two-level typed terms to untyped lambda calculus

open import Data.Nat hiding (_<_)
open import Data.Bool
open import Data.Fin hiding (_≤_ ; pred; _+_)
open import Data.List
open import Data.Product

open import Function
open import Algebra.FunctionProperties using (Commutative; Identity; RightIdentity)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open PropEq.≡-Reasoning
open import Data.Nat.Properties

-- Binding times
data BT : Set where
  S : BT
  D : BT

-- defining a data type [BT],where two members are
-- [S] standing for "static" and [D] standing for dynamic.

-- ``subsumption'' binding times; static can be treated as dynamic,
-- but not vice versa
_≼_ : BT → BT → Bool
_≼_ D S  = false
_≼_ _ _  = true

record True : Set where
data False : Set where

isTrue : Bool → Set
isTrue true  = True
isTrue false = False

-- More general purpose definitions (should also be in standard library)
-- list membership
infix 4 _∈_
data _∈_ {A : Set} : A → List A → Set where
  hd : ∀ {x xs} → x ∈ (x ∷ xs)
  tl : ∀ {x y xs} → x ∈ xs → x ∈ (y ∷ xs)


-- Types of the calculus
mutual
  -- s ^ BT
  data AType : Set where
    Ann : BT → SType → AType

  -- int | t -> t
  data SType : Set where
    SInt  : SType
    SFun  : AType → AType → SType

-- aux definitions
ATInt : BT → AType
ATInt bt = Ann bt SInt
ATFun  : BT → AType → AType → AType
ATFun  bt at1 at2 = Ann bt (SFun at1 at2)

-- projection: get the BT from a type
btof : AType → BT
btof (Ann bt _) = bt

-- well-formedness
data wft : AType → Set where
  wf-int  : ∀ {bt} → wft (Ann bt SInt)
  wf-fun  : ∀ {bt at1 at2} → wft at1 → wft at2
          → isTrue (bt ≼ btof at1) → isTrue (bt ≼ btof at2) → wft (Ann bt (SFun at1 at2))

-- test for dynamic by wellformedness
data IsDynamic : AType → Set where
  is-dyn : ∀ σ → IsDynamic (Ann D σ)

lem-IsDynamic-by-wf : ∀ α → isTrue (D ≼ btof α) → IsDynamic α
lem-IsDynamic-by-wf (Ann S σ) ()
lem-IsDynamic-by-wf (Ann D σ) _ = is-dyn σ 

-- typed annotated expressions
ACtx = List AType

data AExp (Δ : ACtx) : AType → Set where
  AVar : ∀ {α} → α ∈ Δ → AExp Δ α
  AInt : (bt : BT) → ℕ → AExp Δ (ATInt bt)
  ALam : ∀ {α₁ α₂} (bt : BT) → wft (ATFun bt α₂ α₁) → AExp (α₂ ∷ Δ) α₁ → AExp Δ (ATFun bt α₂ α₁)
  AApp : ∀ {α₁ α₂} (bt : BT) → wft (ATFun bt α₂ α₁) → AExp Δ (ATFun bt α₂ α₁) → AExp Δ α₂ → AExp Δ α₁


-- Untyped expression, but correctly scoped
data Exp' : ℕ → Set where
  EVar : ∀ {n} → Fin n → Exp' n
  EInt : ∀ {n} → ℕ → Exp' n
  ELam : ∀ {n} → Exp' (suc n) → Exp' n
  EApp : ∀ {n} → Exp' n → Exp' n → Exp' n

---

m+1+n≡1+m+n : ∀ m n → m + suc n ≡ suc (m + n)
m+1+n≡1+m+n zero    n = refl
m+1+n≡1+m+n (suc m) n = cong suc (m+1+n≡1+m+n m n)

n+0≡n : ∀ n → n + 0 ≡ n
n+0≡n zero    = refl
n+0≡n (suc n) = cong suc $ n+0≡n n

+-comm : ∀ m n → m + n ≡ n + m
+-comm zero    n = sym (n+0≡n n)
+-comm (suc m) n =
  begin
    suc m + n
  ≡⟨ refl ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨ sym (m+1+n≡1+m+n n m) ⟩
    n + suc m
  ∎

≤-refl : ∀ {n} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
≤-trans z≤n q = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

≤-suc-right : ∀ {m n} → m ≤ n → m ≤ suc n
≤-suc-right z≤n = z≤n
≤-suc-right (s≤s p) = s≤s (≤-suc-right p)

≤-suc-left : ∀ {m n} → suc m ≤ n → m ≤ n
≤-suc-left (s≤s p) = ≤-suc-right p

xlate : ∀ {m} {n} → Exp' (m + suc n) → Exp' (suc (n + m))
xlate {m} {n} e rewrite m+1+n≡1+m+n m n | +-comm m n = e

shifter1 : ∀ {n} m → Exp' (suc n) → Exp' (suc (n + m))
shifter1 {n} m (EVar x) = xlate {m} (EVar (raise m x)) 
shifter1 m (EInt x) = EInt x
shifter1 m (ELam e) = ELam (shifter1 m e)
shifter1 m (EApp e e₁) = EApp (shifter1 m e) (shifter1 m e₁)

shifter0 : ∀ m → Exp' zero → Exp' m
shifter0 m (EVar ())
shifter0 m (EInt x) = EInt x
shifter0 m (ELam e) = ELam (shifter1 m e)
shifter0 m (EApp e e₁) = EApp (shifter0 m e) (shifter0 m e₁)

shifter : ∀ m d → Exp' m → Exp' (m + d)
shifter zero d e = shifter0 d e
shifter (suc m) d e = shifter1 d e

-- m+n∸m≡n : ∀ {m n} → m ≤ n → m + (n ∸ m) ≡ n
-- m+n∸m≡n p

helper : ∀ {m n} → n ≤ m → Exp' (n + (m ∸ n)) → Exp' m
helper p e rewrite m+n∸m≡n p = e


-- index m = nesting level of dynamic definitions
Imp : (m : ℕ) → AType → Set
Imp m (Ann S SInt) = ℕ
Imp m (Ann S (SFun α₁ α₂)) = ∀ n → m ≤ n → (Imp n α₁ → Imp n α₂)
Imp m (Ann D σ) = Exp' m

-- index = nesting level of dynamic definitions
data AEnv1 : ℕ → ACtx → Set where
  [] : AEnv1 0 []
  consS : ∀ {m Δ o} → m ≤ o → (α : AType) → Imp o α → AEnv1 m Δ → AEnv1 o (α ∷ Δ)
  consD : ∀ {m Δ} → (α : AType) → isTrue (D ≼ btof α) → Imp (suc m) α → AEnv1 m Δ → AEnv1 (suc m) (α ∷ Δ)

lift1 : ∀ {m n} α → m ≤ n → Imp m α → Imp n α 
lift1 (Ann S SInt) p v = v
lift1 (Ann S (SFun x x₁)) p v = λ k n≤k → v k (≤-trans p n≤k)
lift1 {m} {n} (Ann D σ) p v = helper p (shifter m (n ∸ m) v)

lookup1 : ∀ {α Δ m n} → m  ≤ n → AEnv1 m Δ → α ∈ Δ → Imp n α
lookup1 {α} p (consS _ .α x env) hd = lift1 α p x
lookup1 {α} p (consD .α x x₁ env) hd = lift1 α p x₁
lookup1 p (consS p' .y x env) (tl {_} {y} x₁) = lookup1 (≤-trans p' p) env x₁
lookup1 p (consD .y x x₁ env) (tl {_} {y} x₂) = lookup1 (≤-suc-left p) env x₂

pe1 : ∀ {α Δ} m → AExp Δ α → AEnv1 m Δ → Imp m α
pe1 m (AVar x) env = lookup1 ≤-refl env x
pe1 m (AInt S x) env = x
pe1 m (AInt D x) env = EInt x
pe1 m (ALam S x e) env = λ o p → λ v → pe1 o e (consS p _ v env)
pe1 m (ALam {α₂} {α₁} D (wf-fun w₁ w₂ d≤bt₁ d≤bt₂) e) env 
  with lem-IsDynamic-by-wf α₁ d≤bt₁ | lem-IsDynamic-by-wf α₂ d≤bt₂ 
pe1 m (ALam {.(Ann D σ₂)} {.(Ann D σ₁)} D (wf-fun _ _ d≤bt₁ d≤bt₂) e) env
  | is-dyn σ₁ | is-dyn σ₂ = ELam (pe1 (suc m) e (consD (Ann D σ₁) d≤bt₁ (EVar zero) env))
pe1 m (AApp S x e e₁) env = (pe1 m e env) m ≤-refl (pe1 m e₁ env)
pe1 m (AApp {α₂} {α₁} D (wf-fun w₁ w₂ d≤bt₁ d≤bt₂) e e₁) env 
  with lem-IsDynamic-by-wf α₁ d≤bt₁ | lem-IsDynamic-by-wf α₂ d≤bt₂ 
pe1 m (AApp {.(Ann D σ₂)} {.(Ann D σ₁)} D (wf-fun w₁ w₂ d≤bt₁ d≤bt₂) e e₁) env
  | is-dyn σ₁ | is-dyn σ₂ = EApp (pe1 m e env) (pe1 m e₁ env)
