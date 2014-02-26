module BTA10 where
----------------------------------------
--equivalence between two typing systems
----------------------------------------
------------
--system one
------------
  --  module annotated-type-one where
  --  open import Data.Bool
  --  open import Data.List
  --  open import Data.Nat

  --  infix 4 _∈_
  --  data _∈_ {A : Set} : A → List A → Set where
  --    hd : ∀ {x xs} → x ∈ (x ∷ xs)
  --    tl : ∀ {x y xs} → x ∈ xs → x ∈ (y ∷ xs)
   
  --  data BT : Set where
  --    S : BT
  --    D : BT


  --  data _⊑_ : BT → BT → Set where
  --    bt-refl   : ∀ {bt} → bt ⊑ bt
  --    bt-≤-dyn  : ∀ {bt} → bt ⊑ D

  --  data atype : BT → Set where
  --   AInt : (bt : BT) → atype bt
  --   AFun : (bt : BT) → ∀ {bt₁ bt₂} → atype bt₁ → atype bt₂ → bt ⊑ bt₁ → bt ⊑ bt₂ → atype bt
  --   ⊎ : (bt : BT) → ∀ {bt₁ bt₂} → atype bt₁ → atype bt₂ → bt ⊑ bt₁ → bt ⊑ bt₂ → atype bt
  --   • : (bt : BT) → ∀ {bt₁ bt₂} → atype bt₁ → atype bt₂ → bt ⊑ bt₁ → bt ⊑ bt₂ → atype bt

  --  -- btof : ∀ {bt : BT} → atype bt → BT
  --  -- btof (AInt bt) = bt
  --  -- btof (AFun bt ty ty₁ x x₁) = bt
  --  -- btof (⊎ bt ty ty₁ x x₁) = bt
  --  -- btof (• bt ty ty₁ x x₁) = bt
   
  --  ----------------
  --  --typing context 
  --  ----------------
  --  ----------------------
  --  --auxiliary definition
  --  ----------------------
  --  record Sg (S : Set) (T : S → Set) : Set where
  --    constructor _,_
  --    field
  --      ffst : S
  --      ssnd : T ffst
  --  open Sg public

  --  _of_ : (BT : Set) → (BT → Set) → Set
  --  BT of atype = Sg BT \ x → atype x

  --  AType : Set
  --  AType = BT of atype

  --  ---------
  --  --context
  --  ---------
  --  ACtx = List AType

  
   
  --  ---------
  --  --example
  --  ---------
  --  context1 : ACtx
  --  context1 = (D , AInt D) ∷ (S , AInt S) ∷ (S , AFun S (AInt D) (AInt D) bt-≤-dyn bt-≤-dyn) ∷ [] 
      
  --  ------------------
  --  --typed expression
  --  ------------------
  --  data AExp (Δ : ACtx) : AType → Set where
  --    Var : ∀ {α} → α ∈ Δ → AExp Δ α
  --    Int : (bt : BT) → ℕ → AExp Δ (bt , AInt bt)
  --    Add : ∀ {bt₁ bt₂} → (bt : BT) → AExp Δ (bt₁ , AInt bt₁) → AExp Δ (bt₂ , AInt bt₂) 
  --                      → bt ⊑ bt₁ → bt ⊑ bt₂ → AExp Δ (bt , AInt bt)
  --    ALam : ∀ {b b' : BT} {α₁ : atype b} {α₂ : atype b'}  → (bt : BT)  → AExp ((b , α₁) ∷ Δ) (b' , α₂) 
  --                      → (e₁ : bt ⊑ b) → (e₂ : bt ⊑ b') → AExp Δ (bt , AFun bt α₁ α₂ e₁ e₂)
  --    AApp : ∀ {b b' bt : BT} {α₁ : atype b} {α₂ : atype b'} {e₁ : bt ⊑ b} {e₂ : bt ⊑ b'}  → AExp Δ (bt , AFun bt α₁ α₂ e₁ e₂) 
  --                      → AExp Δ (b , α₁) → AExp Δ (b' , α₂)
  -- -- Static pairs and sums
  --    _,_  : ∀ {b b' bt : BT} {α₁ : atype b} {α₂ : atype b'} → AExp Δ (b , α₁) → AExp Δ (b' , α₂) 
  --                     → (e₁ : bt ⊑ b) → (e₂ : bt ⊑ b') → AExp Δ (bt , • bt α₁ α₂ e₁ e₂)
  --    Tl   : ∀ {b b' bt : BT} {α₁ : atype b} {α₂ : atype b'} → AExp Δ (b , α₁) → (e₁ : bt ⊑ b) → (e₂ : bt ⊑ b') 
  --                     → AExp Δ (bt , ⊎ bt α₁ α₂ e₁ e₂)
  --    Tr   : ∀ {b b' bt : BT} {α₁ : atype b} {α₂ : atype b'} → AExp Δ (b' , α₂) → (e₁ : bt ⊑ b) → (e₂ : bt ⊑ b') 
  --                     → AExp Δ (bt , ⊎ bt α₁ α₂ e₁ e₂)
  --    Fst  : ∀ {b b' bt : BT} {α₁ : atype b} {α₂ : atype b'} {e₁ : bt ⊑ b} {e₂ : bt ⊑ b'} → AExp Δ (bt , • bt α₁ α₂ e₁ e₂) → AExp Δ (b , α₁)
  --    Snd  : ∀ {b b' bt : BT} {α₁ : atype b} {α₂ : atype b'} {e₁ : bt ⊑ b} {e₂ : bt ⊑ b'} → AExp Δ (bt , • bt α₁ α₂ e₁ e₂) → AExp Δ (b' , α₂)
  --    Case : ∀ {b b' b'' bt : BT} {α₁ : atype b} {α₂ : atype b'} {α₃ : atype b''} {e₁ : bt ⊑ b} {e₂ : bt ⊑ b'} 
  --                                 → AExp Δ (bt , ⊎ bt α₁ α₂ e₁ e₂) → AExp ((b , α₁) ∷ Δ) (b'' , α₃) 
  --                                 → AExp ((b' , α₂) ∷ Δ) (b'' , α₃)
  --                                 → bt ⊑ b'' → AExp Δ (b'' , α₃) 
  -- -- Liftable static terms
  -- -- ↑     : ∀ {α} → Liftable α → AExp Δ α  → AExp Δ (D (typeof α))  

------------
--system two
------------

   module annotated-type-two where
   open import Data.Bool
   open import Data.List
   open import Data.Nat

   data BT : Set where
     S : BT
     D : BT
    
   ------------------------------
   --binding time annotated types
   ------------------------------
   ------------------------------
   --Note
   --[BType] for base type 
   --[AType] for annotated type
   ------------------------------
   mutual
     data AType : Set where
       an  : BT → BType → AType
      
     data BType : Set where
       BInt : BType
       BFun : AType → AType → BType
       _•_  : AType → AType → BType 
       _⊎_  : AType → AType → BType 
   
   ACtx = List AType
   
   ------------------
   --well-formed type
   ------------------
   ---------------------
   --auxiliaries
   ---------------------
   btof : AType → BT
   btof (an x x₁) = x

   data _⊑_ : BT → BT → Set where
     refl : ∀ {a : BT} → a ⊑ a
     *≤D  : ∀ {a : BT} → a ⊑ D
   
   -----
   --wft
   -----  
   data wft  : AType → Set where
     wf-int  : ∀ {a : BT} → wft (an a BInt)
     wf-fun  : ∀ {a : BT} {α₁ α₂ : AType} → wft α₁ → wft α₂ 
               → a ⊑ btof α₁ → a ⊑ btof α₂ → wft (an a (BFun α₁ α₂))
     wf-pair : ∀ {a : BT} {α₁ α₂ : AType} → wft α₁ → wft α₂ 
               → a ⊑ btof α₁ → a ⊑ btof α₂ → wft (an a (α₁ • α₂))  
     wf-sum  : ∀ {a : BT} {α₁ α₂ : AType} → wft α₁ → wft α₂ 
               → a ⊑ btof α₁ → a ⊑ btof α₂ → wft (an a (α₁ ⊎ α₂))