module BTA4 where
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

open import Relation.Nullary

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

-- an inductive type describing bt subsumption
data _⊑_ : BT → BT → Set where
  bt-leq-refl : ∀ {bt} → bt ⊑ bt
  bt-leq-dyn  : ∀ {bt} → bt ⊑ D

bt-reify : ∀ bt1 bt2 → isTrue (bt1 ≼ bt2) → bt1 ⊑ bt2
bt-reify S S p = bt-leq-refl
bt-reify S D p = bt-leq-dyn
bt-reify D S ()
bt-reify D D p = bt-leq-refl

bt-reflect : ∀ bt1 bt2 → bt1 ⊑ bt2 → isTrue (bt1 ≼ bt2)
bt-reflect S S p = _
bt-reflect S D p = _
bt-reflect D S ()
bt-reflect D D p = _

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

-- an alternative: have only wf types from the start
data AType' : BT → Set where
  AInt : (bt : BT) → AType' bt
  AFun : (bt : BT) → ∀ {bt1 bt2} → AType' bt1 → AType' bt2 → bt ⊑ bt1 → bt ⊑ bt2 → AType' bt

forget-wft : ∀ {bt} → AType' bt → AType
forget-wft {bt} (AInt .bt) = ATInt bt
forget-wft {bt} (AFun .bt at at₁ x x₁) = ATFun bt (forget-wft at) (forget-wft at₁)

data LEQ-Problem : Set where
  LEQ-not-D⊑S : LEQ-Problem

data WF-Problem : Set where
  WF-LEQ-right : LEQ-Problem → WF-Problem
  WF-LEQ-left : LEQ-Problem → WF-Problem
  WF-WF-left : WF-Problem → WF-Problem
  WF-WF-right : WF-Problem → WF-Problem

data Inferred (E A : Set) : Set where
  Ok : A → Inferred E A
  Error : E → Inferred E A

infer-bt-leq : ∀ bt1 bt2 → Inferred LEQ-Problem (bt1 ⊑ bt2)
infer-bt-leq S S = Ok bt-leq-refl
infer-bt-leq S D = Ok bt-leq-dyn
infer-bt-leq D S = Error LEQ-not-D⊑S
infer-bt-leq D D = Ok bt-leq-refl

-- insufficiently constrained ...
infer-wft' : (α : AType) → Inferred WF-Problem (AType' (btof α))
infer-wft' (Ann x SInt) = Ok (AInt x)
infer-wft' (Ann x (SFun x₁ x₂)) with infer-wft' x₁ | infer-wft' x₂ | infer-bt-leq x (btof x₁) | infer-bt-leq x (btof x₂)
infer-wft' (Ann x₄ (SFun x₁ x₂)) | Ok x | Ok x₃ | Ok x₅ | Ok x₆ = Ok (AFun x₄ x x₃ x₅ x₆)
infer-wft' (Ann x₄ (SFun x₁ x₂)) | Ok x | Ok x₃ | Ok x₅ | Error x₆ = Error (WF-LEQ-right x₆)
infer-wft' (Ann x₄ (SFun x₁ x₂)) | Ok x | Ok x₃ | Error x₅ | okbt2 = Error (WF-LEQ-left x₅)
infer-wft' (Ann x₄ (SFun x₁ x₂)) | Ok x | Error x₃ | _ | _ = Error (WF-WF-right x₃)
infer-wft' (Ann x₃ (SFun x₁ x₂)) | Error x | r2 | _ | _ = Error (WF-WF-left x)

-- might be easier to infer a Σ type
check-wft : (α : AType) → Inferred WF-Problem (∃ λ α' → α ≡ forget-wft {btof α} α')
check-wft (Ann x SInt) = Ok (AInt x , refl)
check-wft (Ann x (SFun x₁ x₂)) with check-wft x₁ | check-wft x₂ | infer-bt-leq x (btof x₁) | infer-bt-leq x (btof x₂)
... | Ok (α₁ , pr₁) | Ok (α₂ , pr₂) | Ok leq₁ | Ok leq₂ = Ok (AFun x α₁ α₂ leq₁ leq₂ , cong₂ (λ x₃ x₄ → Ann x (SFun x₃ x₄)) pr₁ pr₂)
... | Ok p₁ | Ok p₂ | Ok leq₁ | Error e₄ = Error (WF-LEQ-right e₄)
... | Ok p₁ | Ok p₂ | Error e₃ | _ = Error (WF-LEQ-left e₃)
... | Ok p₁ | Error e₂ | _ | _ = Error (WF-WF-right e₂)
... | Error e₁ | _ | _ | _ = Error (WF-WF-left e₁)


unfold-forget : ∀ bt {bt₁} {bt₂} at₁ at₂ x₅ x₆ →
  forget-wft (AFun bt  {bt₁} {bt₂} at₁ at₂ x₅ x₆) ≡ ATFun bt (forget-wft at₁) (forget-wft at₂)
unfold-forget bt at₁ at₂ x₅ x₆ = refl


-- well-formedness
data wft : AType → Set where
  wf-int  : ∀ {bt} → wft (Ann bt SInt)
  wf-fun  : ∀ {bt at1 at2} → wft at1 → wft at2
          → isTrue (bt ≼ btof at1) → isTrue (bt ≼ btof at2) → wft (Ann bt (SFun at1 at2))

infer-lemma-fun-left : ∀ σ₁ α₂ → ¬ wft (Ann D (SFun (Ann S σ₁) α₂)) 
infer-lemma-fun-left σ₁ α₂ (wf-fun v v₁ () x₁)

infer-lemma-fun-right : ∀ α σ → ¬ wft (Ann D (SFun α (Ann S σ))) 
infer-lemma-fun-right α σ (wf-fun v v₁ x ())


infer-yes-yes : ∀ bt α₁ α₂ → (wf1 : wft α₁) (wf2 : wft α₂) → Dec (wft (Ann bt (SFun α₁ α₂)))
infer-yes-yes S (Ann bt1 σ₁) (Ann bt2 σ₂) wf1 wf2 = yes (wf-fun wf1 wf2 _ _)
infer-yes-yes D (Ann D σ₁) (Ann D σ₂) wf1 wf2     = yes (wf-fun wf1 wf2 _ _)
infer-yes-yes D (Ann S σ₁) (Ann bt2 σ₂) wf1 wf2   = no (infer-lemma-fun-left σ₁ (Ann bt2 σ₂))
infer-yes-yes D (Ann bt1 σ₁) (Ann S σ₂) wf1 wf2   = no (infer-lemma-fun-right (Ann bt1 σ₁) σ₂)



infer-lemma-arg-left : ∀ bt α₁ α₂ → ¬ wft α₁ → ¬ wft (Ann bt (SFun α₁ α₂))
infer-lemma-arg-left bt α₁ α₂ ¬wft1 (wf-fun v v₁ x x₁) = ¬wft1 v

infer-lemma-arg-right : ∀ bt α₁ α₂ → ¬ wft α₂ → ¬ wft (Ann bt (SFun α₁ α₂))
infer-lemma-arg-right bt α₁ α₂ ¬wft2 (wf-fun v v₁ x x₁) = ¬wft2 v₁


infer-wft : (α : AType) → Dec (wft α)
infer-wft (Ann bt SInt) = yes wf-int
infer-wft (Ann bt (SFun α₁ α₂)) 
  with infer-wft α₁ | infer-wft α₂
... | yes wf1 | yes wf2 = infer-yes-yes bt α₁ α₂ wf1 wf2
... | yes wf1 | no ¬wf2 = no (infer-lemma-arg-right bt α₁ α₂ ¬wf2)
... | no ¬wf1 | yes wf2 = no (infer-lemma-arg-left bt α₁ α₂ ¬wf1)
... | no ¬wf1 | no ¬wf2 = no (infer-lemma-arg-left bt α₁ α₂ ¬wf1)

----------------------------------------------------------------------
-- step 0
-- Untyped expressions, incorrect results
data Exp : Set where
  EVar : ℕ → Exp
  EInt : ℕ → Exp
  EAdd : Exp → Exp → Exp
  ELam : Exp → Exp
  EApp : Exp → Exp → Exp

-- mapping from annotated type to implementation type
ImpTA : AType → Set
ImpTA (Ann S SInt) = ℕ
ImpTA (Ann S (SFun α β)) = ImpTA α → ImpTA β
ImpTA (Ann D σ) = Exp

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
  AAdd : (bt : BT) → AExp Δ (ATInt bt) → AExp Δ (ATInt bt) → AExp Δ (ATInt bt)
  ALam : ∀ {α₁ α₂} (bt : BT) → wft (ATFun bt α₂ α₁) → AExp (α₂ ∷ Δ) α₁ → AExp Δ (ATFun bt α₂ α₁)
  AApp : ∀ {α₁ α₂} (bt : BT) → wft (ATFun bt α₂ α₁) → AExp Δ (ATFun bt α₂ α₁) → AExp Δ α₂ → AExp Δ α₁

-- TODO: replace wellformedness of types in AApp with lemma
-- the lemma does not require wft in AApp
data wft-context : ACtx → Set where
  wft-[] : wft-context []
  wft-:: : ∀ {α Δ} → wft α → wft-context Δ → wft-context (α ∷ Δ)

lemma-wft-var : ∀ {α Δ} → wft-context Δ → α ∈ Δ → wft α
lemma-wft-var (wft-:: x wc) hd = x
lemma-wft-var (wft-:: x wc) (tl pf) = lemma-wft-var wc pf

lemma-wft : ∀ {α Δ} → wft-context Δ → AExp Δ α → wft α
lemma-wft wc (AVar x) = lemma-wft-var wc x
lemma-wft wc (AInt bt x) = wf-int
lemma-wft wc (AAdd bt ae₁ ae₂) = wf-int
lemma-wft wc (ALam bt x ae) = x
lemma-wft wc (AApp bt _ ae ae₁)
  with lemma-wft wc ae 
... | (wf-fun w₁ w₂ d≤bt₁ d≤bt₂) = w₂

data AEnv0 (F : AType → Set) : ACtx -> Set where
  AE[] : AEnv0 F []
  AE∷  : ∀ {Δ} α → F α → AEnv0 F Δ → AEnv0 F (α ∷ Δ)

AEnv = AEnv0 ImpTA

aelength : ∀ {F Δ} → AEnv0 F Δ → ℕ
aelength AE[] = 0
aelength (AE∷ α x ae) = suc( aelength ae)

lookup : ∀ {F Δ α} → AEnv0 F Δ → (o : α ∈ Δ ) → F α
lookup (AE∷ α x env) hd = x
lookup (AE∷ α x env) (tl o) = lookup env o


-- partial evaluation
peval : ∀ {α Δ } → AExp Δ α → AEnv Δ → ImpTA α
peval (AVar x) env = lookup env x
peval (AInt S x) env = x
peval (AInt D x) env = EInt x
peval (AAdd S e₁ e₂) env = peval e₁ env + peval e₂ env
peval (AAdd D e₁ e₂) env = EAdd (peval e₁ env) (peval e₂ env)
peval (ALam {α₂} {α₁} S w e) env = λ y → peval e (AE∷ α₁ y env)
peval (ALam {α₂} {α₁} D (wf-fun w₁ w₂ d≤bt₁ d≤bt₂) e) env 
  with lem-IsDynamic-by-wf α₁ d≤bt₁ | lem-IsDynamic-by-wf α₂ d≤bt₂ 
peval (ALam {.(Ann D σ₂)} {.(Ann D σ₁)} D (wf-fun _ _ d≤bt₁ d≤bt₂) e) env
  | is-dyn σ₁ | is-dyn σ₂ = ELam (peval e (AE∷ (Ann D σ₁) (EVar (aelength env)) env))
peval (AApp S w e e₁) env = peval e env (peval e₁ env)
peval (AApp {α₂} {α₁} D (wf-fun w₁ w₂ d≤bt₁ d≤bt₂) e e₁) env 
  with lem-IsDynamic-by-wf α₁ d≤bt₁ | lem-IsDynamic-by-wf α₂ d≤bt₂ 
peval (AApp {.(Ann D σ₂)} {.(Ann D σ₁)} D (wf-fun _ _ d≤bt₁ d≤bt₂) e e₁) env 
  | is-dyn σ₁ | is-dyn σ₂ = EApp (peval e env) (peval e₁ env)

----------------------------------------------------------------------
-- step 1
-- Untyped expression, but correctly scoped
data Exp' : ℕ → Set where
  EVar : ∀ {n} → Fin n → Exp' n
  EInt : ∀ {n} → ℕ → Exp' n
  EAdd : ∀ {n} → Exp' n → Exp' n → Exp' n
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
shifter1 m (EAdd e₁ e₂) = EAdd (shifter1 m e₁) (shifter1 m e₂)
shifter1 m (ELam e) = ELam (shifter1 m e)
shifter1 m (EApp e e₁) = EApp (shifter1 m e) (shifter1 m e₁)

shifter0 : ∀ m → Exp' zero → Exp' m
shifter0 m (EVar ())
shifter0 m (EInt x) = EInt x
shifter0 m (EAdd e₁ e₂) = EAdd (shifter0 m e₁) (shifter0 m e₂)
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
pe1 m (AAdd S e₁ e₂) env = pe1 m e₁ env + pe1 m e₂ env
pe1 m (AAdd D e₁ e₂) env = EAdd (pe1 m e₁ env) (pe1 m e₂ env)
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


term1 : AExp [] (ATInt D)
term1 = AInt D 42

term2 : AExp [] (ATFun D (ATInt D) (ATInt D))
term2 = ALam D (wf-fun wf-int wf-int _ _) (AVar hd)
-- Dλ y → let f = λ x → x D+ y in Dλ z → f z
-- Dλ y → let f = λ x → (Dλ w → x D+ y) in Dλ z → f z
-- Dλ y → (λ f → Dλ z → f z) (λ x → (Dλ w → x D+ y))
-- :: DInt D→ (DT  D→ DInt)
-- y : DInt, f : DInt → (DT  D→ DInt)

term3-0 : AExp (Ann D SInt ∷ Ann D SInt ∷ Ann D SInt ∷ []) (Ann D SInt)
term3-0 = AAdd D (AVar (tl (tl hd))) (AVar (tl hd))

term3-1 : AExp (Ann D SInt ∷ Ann D SInt ∷ []) (Ann D (SFun (Ann D SInt) (Ann D SInt)))
term3-1 = ALam D (wf-fun wf-int wf-int _ _) term3-0

term3-2 : AExp (Ann D SInt ∷ []) (Ann S (SFun (Ann D SInt) (Ann D (SFun (Ann D SInt) (Ann D SInt)))))
term3-2 = ALam S (wf-fun wf-int (wf-fun wf-int wf-int _ _) _ _) term3-1


term3-3 : AExp (Ann D SInt ∷ Ann S (SFun (Ann D SInt) (Ann D (SFun (Ann D SInt) (Ann D SInt)))) ∷ Ann D SInt ∷ [])
               (Ann D (SFun (Ann D SInt) (Ann D SInt)))
term3-3 = AApp S (wf-fun wf-int (wf-fun wf-int wf-int _ _) _ _) (AVar (tl hd)) (AVar hd)

term3-4 : AExp (Ann S (SFun (Ann D SInt) (Ann D (SFun (Ann D SInt) (Ann D SInt)))) ∷ Ann D SInt ∷ [])
               (Ann D (SFun (Ann D SInt) (Ann D (SFun (Ann D SInt) (Ann D SInt)))))
term3-4 = ALam D (wf-fun wf-int (wf-fun wf-int wf-int _ _) _ _) term3-3

term3-5 : AExp (Ann D SInt ∷ [])
               (Ann S (SFun (Ann S (SFun (Ann D SInt) (Ann D (SFun (Ann D SInt) (Ann D SInt)))))
                            (Ann D (SFun (Ann D SInt) (Ann D (SFun (Ann D SInt) (Ann D SInt)))))))
term3-5 = ALam S (wf-fun (wf-fun wf-int (wf-fun wf-int wf-int _ _) _ _) (wf-fun wf-int (wf-fun wf-int wf-int _ _) _ _) _ _) term3-4

term3-6 : AExp (Ann D SInt ∷ [])
               (Ann D (SFun (Ann D SInt) (Ann D (SFun (Ann D SInt) (Ann D SInt)))))
term3-6 = AApp S (wf-fun (wf-fun wf-int (wf-fun wf-int wf-int _ _) _ _) (wf-fun wf-int (wf-fun wf-int wf-int _ _) _ _) _ _) term3-5 term3-2

term3 : AExp [] (Ann D (SFun (Ann D SInt) (Ann D (SFun (Ann D SInt) (Ann D (SFun (Ann D SInt) (Ann D SInt)))))))
term3 = ALam D (wf-fun wf-int (wf-fun wf-int (wf-fun wf-int wf-int _ _) _ _) _ _) term3-6


-- conclusion: you want type inference ...


-------------------------------------------------------------------------------
-- step 2
-- now let's do everything typed

data Type : Set where
  Int : Type
  Fun : Type → Type → Type

Ctx = List Type

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

-- erase annotations
erase : AType → Type
erase (Ann x SInt) = Int
erase (Ann x (SFun x₁ x₂)) = Fun (erase x₁) (erase x₂)

-- index Γ = nesting level of dynamic definitions / dynamic environment
Imp'' : Ctx → AType → Set
Imp'' Γ (Ann S SInt) = ℕ
Imp'' Γ (Ann S (SFun α₁ α₂)) = ∀ Γ' → Γ ↝ Γ' → (Imp'' Γ' α₁ → Imp'' Γ' α₂)
Imp'' Γ (Ann D σ) = Exp'' Γ (erase (Ann D σ))

-- index = nesting level of dynamic definitions
data AEnv2 : Ctx → ACtx → Set where
  [] : AEnv2 [] []
  consS : ∀ {Γ Δ Γ'} → Γ ↝ Γ' → (α : AType) → Imp'' Γ' α → AEnv2 Γ Δ → AEnv2 Γ' (α ∷ Δ)
  consD : ∀ {Γ Δ} → (α : AType) → isTrue (D ≼ btof α) → Imp'' (erase α ∷ Γ) α → AEnv2 Γ Δ → AEnv2 (erase α ∷ Γ) (α ∷ Δ)


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
lift2 (Ann S SInt) p v = v
lift2 (Ann S (SFun x x₁)) Γ↝Γ' v = λ Γ'' Γ'↝Γ'' → v Γ'' (↝-trans Γ↝Γ' Γ'↝Γ'')
lift2 (Ann D x₁) Γ↝Γ' v = elevate (↝↝-base Γ↝Γ') v

lookup2 : ∀ {α Δ Γ Γ'} → Γ ↝ Γ' → AEnv2 Γ Δ → α ∈ Δ → Imp'' Γ' α
lookup2 Γ↝Γ' (consS p α v env) hd = lift2 α Γ↝Γ' v
lookup2 Γ↝Γ' (consS p α₁ v env) (tl x) = lookup2 (↝-trans p Γ↝Γ') env x
lookup2 Γ↝Γ' (consD α D≼α v env) hd = lift2 α Γ↝Γ' v
lookup2 ↝-refl (consD α₁ D≼α v env) (tl x) = lookup2 (↝-extend ↝-refl) env x
lookup2 (↝-extend Γ↝Γ') (consD α₁ D≼α v env) (tl x) = lookup2 (lem (erase α₁) _ _ _ Γ↝Γ') env x

pe2 : ∀ {α Δ} Γ → AExp Δ α → AEnv2 Γ Δ → Imp'' Γ α
pe2 Γ (AVar x) env = lookup2 ↝-refl env x
pe2 Γ (AInt S x) env = x
pe2 Γ (AInt D x) env = EInt x
pe2 Γ (AAdd S e₁ e₂) env = pe2 Γ e₁ env + pe2 Γ e₂ env
pe2 Γ (AAdd D e₁ e₂) env = EAdd (pe2 Γ e₁ env) (pe2 Γ e₂ env)
pe2 {Ann S (SFun α₂ α₁)} Γ (ALam .S w e) env = λ Γ' Γ↝Γ' → λ y → pe2 {α₁} Γ' e (consS Γ↝Γ' α₂ y env)
pe2 Γ (ALam {α₂} {α₁} D (wf-fun w₁ w₂ d≤bt₁ d≤bt₂) e) env 
  with lem-IsDynamic-by-wf α₁ d≤bt₁ | lem-IsDynamic-by-wf α₂ d≤bt₂ 
pe2 Γ (ALam {.(Ann D σ₂)} {.(Ann D σ₁)} D (wf-fun _ _ d≤bt₁ d≤bt₂) e) env
  | is-dyn σ₁ | is-dyn σ₂ = ELam (pe2 (erase (Ann D σ₁) ∷ Γ) e (consD (Ann D σ₁) d≤bt₁ (EVar hd) env))
pe2 Γ (AApp S w e₁ e₂) env = pe2 Γ e₁ env Γ ↝-refl (pe2 Γ e₂ env)
pe2 Γ (AApp {α₂} {α₁} D (wf-fun w₁ w₂ d≤bt₁ d≤bt₂) e e₁) env 
  with lem-IsDynamic-by-wf α₁ d≤bt₁ | lem-IsDynamic-by-wf α₂ d≤bt₂ 
pe2 Γ (AApp {.(Ann D σ₂)} {.(Ann D σ₁)} D (wf-fun w₁ w₂ d≤bt₁ d≤bt₂) e e₁) env
  | is-dyn σ₁ | is-dyn σ₂ = EApp (pe2 Γ e env) (pe2 Γ e₁ env)

pe2-term1 = pe2 [] term1 []
pe2-term2 = pe2 [] term2 []
pe2-term3 = pe2 [] term3 [] 
