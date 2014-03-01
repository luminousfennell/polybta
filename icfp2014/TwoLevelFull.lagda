\agdaIgnore{
\begin{code}
module TwoLevelFull where
open import Lib
open import BaseFull
open import CtxExtension

data AType : Set where
  SNum  : AType
  SFun  : AType → AType → AType
\end{code}}
\agdaSnippet\btaATypeSumProd{
\begin{code}
  SPrd  : AType → AType → AType
  SSum  : AType → AType → AType
\end{code}}
\agdaIgnore{
\begin{code}
  D     : Type → AType

ACtx = List AType



-- The mapping from annotated types to residual types is straightforward.
erase : AType → Type
erase SNum = Num
erase (SFun α₁ α₂) = Fun (erase α₁) (erase α₂)
erase (SPrd α₁ α₂) = Prd (erase α₁) (erase α₂)
erase (SSum α₁ α₂) = Sum (erase α₁) (erase α₂)
erase (D x) = x

\end{code}}
\agdaSnippet\btaLiftable{
\begin{code}
mutual 
  data Liftable : AType → Set where
    D : ∀ τ → Liftable (D τ)
    SCst : Liftable SNum
    SSum : ∀ {α₁ α₂} →
      Liftable α₁ → Liftable α₂ → Liftable (SSum α₁ α₂)
    SPrd : ∀ {α₁ α₂} →
      Liftable α₁ → Liftable α₂ → Liftable (SPrd α₁ α₂)
    SFun : ∀ {α₁ α₂} →
      Liftable⁻ α₁ → Liftable α₂ → Liftable (SFun α₁ α₂)

  data Liftable⁻ : AType → Set where
    D : ∀ τ → Liftable⁻ (D τ)
    SPrd : ∀ {α₁ α₂} →
      Liftable⁻ α₁ → Liftable⁻ α₂ → Liftable⁻ (SPrd α₁ α₂)
    SFun : ∀ {α₁ α₂} →
      Liftable α₁ → Liftable⁻ α₂ → Liftable⁻ (SFun α₁ α₂)
\end{code}}
\agdaIgnore{
\begin{code}

data AExp (Δ : ACtx) : AType → Set where
  Var : ∀ {α} → α ∈ Δ → AExp Δ α
  SCst : ℕ → AExp Δ SNum
  SAdd : AExp Δ SNum → AExp Δ SNum → AExp Δ SNum
  SLam : ∀ {α₁ α₂} → AExp (α₁ ∷ Δ) α₂ → AExp Δ (SFun α₁ α₂)
  SApp : ∀ {α₁ α₂} → AExp Δ (SFun α₁ α₂) → AExp Δ α₁ → AExp Δ α₂
  DCst : ℕ → AExp Δ (D Num)
  DAdd : AExp Δ (D Num) → AExp Δ (D Num) → AExp Δ (D Num)
  DLam : ∀ {σ₁ σ₂} → AExp ((D σ₁) ∷ Δ) (D σ₂) → AExp Δ (D (Fun σ₁ σ₂))
  DApp : ∀ {σ₁ σ₂} → AExp Δ (D (Fun σ₂ σ₁)) → AExp Δ (D σ₂) → AExp Δ (D σ₁)
  -- Dynamic pairs and sums
\end{code}}
\agdaSnippet\btaAExpSumProd{
\begin{code}
  SPair : ∀ {α₁ α₂} → AExp Δ α₁ → AExp Δ α₂ → AExp Δ (SPrd α₁ α₂)
  SInl   : ∀ {α₁ α₂} → AExp Δ α₁ → AExp Δ (SSum α₁ α₂)
  SInr   : ∀ {α₁ α₂} → AExp Δ α₂ → AExp Δ (SSum α₁ α₂)
  SFst  : ∀ {α₁ α₂} → AExp Δ (SPrd α₁ α₂) → AExp Δ α₁
  SSnd  : ∀ {α₁ α₂} → AExp Δ (SPrd α₁ α₂) → AExp Δ α₂
  SCase : ∀ {α₁ α₂ α₃} → AExp Δ (SSum α₁ α₂) → AExp (α₁ ∷ Δ) α₃ → AExp (α₂ ∷ Δ) α₃ → AExp Δ α₃
  DPair  : ∀ {σ₁ σ₂} → AExp Δ (D σ₁) → AExp Δ (D σ₂) → AExp Δ (D (Prd σ₁ σ₂))
  DInl   : ∀ {σ₁ σ₂} → AExp Δ (D σ₁) → AExp Δ (D (Sum σ₁ σ₂))
  DInr   : ∀ {σ₁ σ₂} → AExp Δ (D σ₂) → AExp Δ (D (Sum σ₁ σ₂))
  DFst  : ∀ {σ₁ σ₂} → AExp Δ (D (Prd σ₁ σ₂)) → AExp Δ (D σ₁)
  DSnd  : ∀ {σ₁ σ₂} → AExp Δ (D (Prd σ₁ σ₂)) → AExp Δ (D σ₂)
  DCase : ∀ {σ₁ σ₂ σ₃} → AExp Δ (D (Sum σ₁ σ₂)) → AExp ((D σ₁) ∷ Δ) (D σ₃) → AExp ((D σ₂) ∷ Δ) (D σ₃) → AExp Δ (D σ₃) 
\end{code}}
\agdaSnippet\btaAExpLift{
\begin{code}
  Lift : {α : AType} →
    Liftable α → AExp Δ α  → AExp Δ (D (erase α))
\end{code}}
\agdaIgnore{
\begin{code}

-- type interpretation
ATInt : Ctx → AType → Set
ATInt _ SNum          = ℕ
ATInt Γ (D σ)         = Exp Γ σ
ATInt Γ (SFun α₁ α₂)  =
  ∀ {Γ'} → Γ ↝ Γ' → ATInt Γ' α₁ → ATInt Γ' α₂
ATInt Γ (SPrd α₁ α₂) = ATInt Γ α₁ × ATInt Γ α₂
ATInt Γ (SSum α₁ α₂) = (ATInt Γ α₁) ⊎ (ATInt Γ α₂)

data AEnv (Γ : Ctx) : ACtx → Set where
  [] : AEnv Γ []
  _∷_ : ∀ {α Δ} → ATInt Γ α → AEnv Γ Δ → AEnv Γ (α ∷ Δ)

elevate-var : ∀ {Γ Γ'} {τ : Type} → Γ ↝ Γ' → τ ∈ Γ → τ ∈ Γ'
elevate-var refl x = x
elevate-var (extend Γ↝Γ') x = tl (elevate-var Γ↝Γ' x)

elevate-var2 : ∀ {Γ Γ' Γ'' τ} → Γ ↝ Γ' ↝ Γ'' → τ ∈ Γ → τ ∈ Γ''
elevate-var2 (refl x) x₁ = elevate-var x x₁
elevate-var2 (extend Γ↝Γ'↝Γ'') hd = hd
elevate-var2 (extend Γ↝Γ'↝Γ'') (tl x) = tl (elevate-var2 Γ↝Γ'↝Γ'' x)

elevate : ∀ {Γ Γ' Γ'' τ} → Γ ↝ Γ' ↝ Γ'' → Exp Γ τ → Exp Γ'' τ
elevate Γ↝Γ'↝Γ'' (EVar x) = EVar (elevate-var2 Γ↝Γ'↝Γ'' x)
elevate Γ↝Γ'↝Γ'' (ECst x) = ECst x
elevate Γ↝Γ'↝Γ'' (EAdd e e₁) = EAdd (elevate Γ↝Γ'↝Γ'' e) (elevate Γ↝Γ'↝Γ'' e₁)
elevate Γ↝Γ'↝Γ'' (ELam e) = ELam (elevate (extend Γ↝Γ'↝Γ'') e)
elevate Γ↝Γ'↝Γ'' (EApp e e₁) = EApp (elevate Γ↝Γ'↝Γ'' e) (elevate Γ↝Γ'↝Γ'' e₁)
elevate Γ↝Γ'↝Γ'' (EPair e e₁) =  EPair (elevate Γ↝Γ'↝Γ'' e) (elevate Γ↝Γ'↝Γ'' e₁)
elevate Γ↝Γ'↝Γ'' (EInl e) = EInl (elevate Γ↝Γ'↝Γ'' e)
elevate Γ↝Γ'↝Γ'' (EInr e) = EInr (elevate Γ↝Γ'↝Γ'' e)
elevate Γ↝Γ'↝Γ'' (EFst e) = EFst (elevate Γ↝Γ'↝Γ'' e)
elevate Γ↝Γ'↝Γ'' (ESnd e) = ESnd (elevate Γ↝Γ'↝Γ'' e)
elevate Γ↝Γ'↝Γ'' (ECase c e₁ e₂) = ECase (elevate Γ↝Γ'↝Γ'' c) (elevate (extend Γ↝Γ'↝Γ'') e₁) (elevate (extend Γ↝Γ'↝Γ'') e₂)
exp↑ : ∀ {τ τ' Γ} → Exp Γ τ' → Exp (τ ∷ Γ) τ'
exp↑ e = elevate (refl (extend refl)) e

int↑ : ∀ { α Γ Γ'} → Γ ↝ Γ' → ATInt Γ α → ATInt Γ' α
int↑ refl v = v
int↑ {D τ} (extend Γ↝Γ') e = exp↑ (int↑ Γ↝Γ' e)
int↑ {SNum} _ v = v
int↑ {SFun α α₁} Γ↝Γ' f =
  λ Γ'↝Γ'' x → f (Γ↝Γ' ⊕ Γ'↝Γ'') x
int↑ {SPrd α α₁} Γ↝Γ' (proj₁ , proj₂) = int↑ Γ↝Γ' proj₁ , int↑ Γ↝Γ' proj₂
int↑ {SSum α α₁} Γ↝Γ' (inj₁ x) = inj₁ (int↑ Γ↝Γ' x)
int↑ {SSum α α₁} Γ↝Γ' (inj₂ y) = inj₂ (int↑ Γ↝Γ' y)

env↑ : ∀ { Δ Γ Γ'} → Γ ↝ Γ' → AEnv Γ Δ → AEnv Γ' Δ
env↑ _ [] = []
env↑ Γ↝Γ' (x ∷ ρ) = int↑ Γ↝Γ' x ∷ env↑ Γ↝Γ' ρ

addFresh : ∀ {τ Γ Δ} → AEnv Γ Δ → AEnv (τ ∷ Γ) (D τ ∷ Δ)
addFresh ρ = EVar hd ∷ env↑ (extend refl) ρ

lookup : ∀ {Γ Δ α} → α ∈ Δ → AEnv Γ Δ → ATInt Γ α
lookup hd (v ∷ _) = v 
lookup (tl x) (_ ∷ ρ) = lookup x ρ

\end{code}}
\agdaSnippet\btaLiftImpl{
\begin{code}
mutual 
  lift : ∀ {Γ α} → Liftable α → ATInt Γ α → (Exp Γ (erase α))
  lift (D τ) v = v
  lift SCst v = ECst v
  lift (SSum ty ty₁) (inj₁ a) = EInl (lift ty a)
  lift (SSum ty ty₁) (inj₂ b) = EInr (lift ty₁ b)
  lift (SPrd ty ty₁) (v1 , v2) = EPair (lift ty v1) (lift ty₁ v2)
  lift (SFun {α₁} ty₁ ty₂) f =
    ELam let x = (embed ty₁ (EVar hd)) in
         lift ty₂ (f (extend refl) x)

  embed : ∀ {Γ α} →
    Liftable⁻ α → Exp Γ (erase α) → (ATInt Γ α)
  embed (D τ) e = e
  embed (SPrd ty ty₁) e = embed ty (EFst e) , embed ty₁ (ESnd e)
  embed {Γ} (SFun {α} ty₁ ty₂) e = 
    λ Γ↝Γ' v₁ → embed ty₂ (EApp (int↑ Γ↝Γ' e) (lift ty₁ v₁))
\end{code}}
\agdaIgnore{
\begin{code}

pe : ∀ { Γ Δ α } → 
         AExp Δ α → AEnv Γ Δ → ATInt Γ α
pe (Var x) ρ       = lookup x ρ
pe (DLam e) ρ      = ELam (pe e (addFresh ρ))
pe (SApp f e) ρ    = (pe f ρ) refl (pe e ρ)
pe (SLam {α} e) ρ  = λ Γ↝Γ' x → pe e (x ∷ env↑ Γ↝Γ' ρ)
pe (DApp f e) ρ    = EApp (pe f ρ) (pe e ρ)
pe (SCst x) _      = x
pe (DCst x) _      = ECst x
pe (SAdd e f) ρ    = (pe e ρ) + (pe f ρ) 
pe (DAdd e f) ρ    = EAdd (pe e ρ) (pe f ρ) 
pe (SPair e e₁) ρ = pe e ρ , pe e₁ ρ
pe (SInl e) ρ = inj₁ (pe e ρ)
pe (SInr e) ρ = inj₂ (pe e ρ)
pe (SFst e) ρ = proj₁ (pe e ρ)
pe (SSnd e) ρ = proj₂ (pe e ρ)
pe (SCase e e₁ e₂) ρ with pe e ρ
... | inj₁ v = pe e₁ (v ∷ ρ)
... | inj₂ v = pe e₂ (v ∷ ρ)
pe (DPair e e₁) ρ = EPair (pe e ρ) (pe e₁ ρ)
pe (DInl e) ρ = EInl (pe e ρ)
pe (DInr e) ρ = EInr (pe e ρ)
pe (DFst e) ρ = EFst (pe e ρ)
pe (DSnd e) ρ = ESnd (pe e ρ)
pe (DCase e e₁ e₂) ρ = ECase (pe e ρ) (pe e₁ (addFresh ρ)) (pe e₂ (addFresh ρ))
\end{code}}
\agdaSnippet\btaPeLift{
\begin{code}
pe (Lift lftbl e) ρ = lift lftbl (pe e ρ)
\end{code}}
