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
   
   module traditional-representation where
   infix 4 _∈_
   data _∈_ {A : Set} : A → List A → Set where
     hd : ∀ {x xs} → x ∈ (x ∷ xs)
     tl : ∀ {x y xs} → x ∈ xs → x ∈ (y ∷ xs)

   data BT : Set where
     S : BT
     D : BT
    
   ------------------------------
   --binding time annotated types
   ------------------------------
   ------------------------------
   --Note
   --[BType] for ?
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
   btof (an a x₁) = a

   data _⊑_ : BT → BT → Set where
     reflS : S ⊑ S
     reflD : D ⊑ D
     S≤D  :  S ⊑ D
   
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
   
   ----------
   --Liftable
   ----------
   -----------------------------------------------------------------
   --Note
   --• liftable defines a subset of annotated expressions whose type
   --  annotation can be "lifted" to "D"
   --• liftable dynamic types are trivially lifted 
   --• assume that we only consider the set of well-formed types
   -----------------------------------------------------------------
   mutual 
     data Liftable : AType → Set where
       --dynamic type can be trivially lifted
       D-aty  : ∀ {σ} → Liftable (an D σ)
       --static integer can be lifted to a dynamic one
       --same holds for static pair and sum 
       S-int  : Liftable (an S BInt)
       S-pair : ∀ {α₁ α₂} → Liftable α₁ → Liftable α₂ 
                          → Liftable (an S (α₁ • α₂))
       S-sum  : ∀ {α₁ α₂} → Liftable α₁ → Liftable α₂
                          → Liftable (an S (α₁ ⊎ α₂))
       --a liftable static functional type must have
       --1. dynamic value as input
       --2. higher-order static value with dynamic output
       --3. higher-order static value as input with no
       --   static inputs  
       S-fun  : ∀ {α₁ α₂} → Liftable⁻ α₁ → Liftable α₂ 
                          → Liftable (an S (BFun α₁ α₂))
     data Liftable⁻ : AType → Set where
       D-aty  : ∀ {σ} → Liftable⁻ (an D σ)
       S-pair : ∀ {α₁ α₂} → Liftable⁻ α₁ → Liftable⁻ α₂ 
                          → Liftable⁻ (an S (α₁ • α₂))
       S-fun  : ∀ {α₁ α₂} → Liftable α₁ → Liftable⁻ α₂ 
                          → Liftable⁻ (an S (BFun α₁ α₂))

   data liftable : AType → Set where
     ↑ : ∀ {α} → wft α → Liftable α → liftable α
   ----------------------------
   --typed annotated expression
   ----------------------------
   ----------------------------------------------------
   --Note
   --constructor name begins with an "A" for "annotated"
   --typing constructor as [AExp]
   --typing context as [Δ]
   --"a" for both expression and type annotation
   --"α" for [AType]
   --"σ" for [BType]
   ----------------------------------------------------
   data AExp (Δ : ACtx) : AType → Set where
     Var   : ∀ {α} → α ∈ Δ → AExp Δ α
     AInt  : (a : BT) → ℕ → AExp Δ (an a BInt)
     AAdd  : (a : BT) → AExp Δ (an a BInt) → AExp Δ (an a BInt) → AExp Δ (an a BInt)
     ALam  : ∀ {α₁ α₂} → (a : BT) → wft (an a (BFun α₁ α₂)) → AExp (α₁ ∷ Δ) α₂ 
                       → AExp Δ (an a (BFun α₁ α₂))
     AApp  : ∀ {α₁ α₂} → (a : BT) → wft (an a (BFun α₁ α₂)) → AExp Δ (an a (BFun α₁ α₂))
                       → AExp Δ α₁ → AExp Δ α₂
     APair : ∀ {α₁ α₂} → (a : BT) → wft (an a (α₁ • α₂))  → AExp Δ α₁ → AExp Δ α₂
                       → AExp Δ (an a (α₁ • α₂))
     ATl   : ∀ {α₁ α₂} → (a : BT) → wft (an a (α₁ ⊎ α₂))  → AExp Δ α₁ 
                       → AExp Δ (an a (α₁ ⊎ α₂))
     ATr   : ∀ {α₁ α₂} → (a : BT) → wft (an a (α₁ ⊎ α₂))  → AExp Δ α₂ 
                       → AExp Δ (an a (α₁ ⊎ α₂))
     ACase : ∀ {α₁ α₂ α₃} {a : BT} → a ⊑ btof α₃ → AExp Δ (an a (α₁ ⊎ α₂)) → AExp (α₁ ∷ Δ) α₃
                       → AExp (α₂ ∷ Δ) α₃ → AExp Δ α₃
     Lift  : ∀ {a} {σ} → liftable (an a σ) → AExp Δ (an a σ) → AExp Δ (an D σ)  
    
     
   module two-level-representation where
   ---------------
   --residual type
   ---------------
   data type : Set where
     Int : type
     Fun : type → type → type
     _•_ : type → type → type   
     _⊎_ : type → type → type   
   
   ----------------
   --annotated type
   ----------------
   ---------------------------------------------
   --Note
   --• static type constructor starting with "S"
   --  except for pair and sum
   --• residual type used for building dynamic  
   --  type 
   ---------------------------------------------
   data atype : Set where
    SInt  : atype
    SFun  : atype → atype → atype
    D     : type  → atype
    _•_   : atype → atype → atype 
    _⊎_   : atype → atype → atype 

   btof-γ : atype → BT
   btof-γ SInt = S
   btof-γ (SFun γ γ₁) = S
   btof-γ (D x) = D
   btof-γ (γ • γ₁) = S
   btof-γ (γ ⊎ γ₁) = S

   actx = List atype
   
   ----------
   --Liftable
   ----------
   --Note
   --"τ" for residual type [type]
   --"γ" for [atype]
   mutual 
     data Liftok : atype → Set where
       D-aty  : ∀ τ → Liftok (D τ)
       S-int  : Liftok SInt
       S-sum  : ∀ {γ₁ γ₂} → Liftok γ₁ → Liftok γ₂ → Liftok (γ₁ ⊎ γ₂)
       S-pair : ∀ {γ₁ γ₂} → Liftok γ₁ → Liftok γ₂ → Liftok (γ₁ • γ₂)
       S-fun  : ∀ {γ₁ γ₂} → Liftok⁻ γ₁ → Liftok γ₂ → Liftok (SFun γ₁ γ₂)

     data Liftok⁻ : atype → Set where
       D-aty : ∀ τ → Liftok⁻ (D τ)
       _•_   : ∀ {γ₁ γ₂} → Liftok⁻ γ₁ → Liftok⁻ γ₂ → Liftok⁻ (γ₁ • γ₂)
       S-fun : ∀ {γ₁ γ₂} → Liftok γ₁ → Liftok⁻ γ₂ → Liftok⁻ (SFun γ₁ γ₂)
   
   ----------------------------
   --typed two-level annotated expression
   ----------------------------
   --------------------
   --auxiliary function
   --------------------
   typeof : atype → type
   typeof SInt = Int
   typeof (SFun γ₁ γ₂) = Fun (typeof γ₁) (typeof γ₂) 
   typeof (D τ) = τ
   typeof (γ₁ • γ₂) = typeof γ₁ • typeof γ₂
   typeof (γ₁ ⊎ γ₂) = typeof γ₁ ⊎ typeof γ₂
   
   --------
   --[aexp]
   --------
   --Note
   --• "γ" for [atype]
   --• "τ" for [type]
   --• typed terms starting with "S" for "static"
   --  and "D" for "dynamic",except for pair
   --• "Ω" for typing context
   data aexp (Ω : actx) : atype → Set where
     Var    : ∀ {γ} → γ ∈ Ω → aexp Ω γ
     SInt   : ℕ → aexp Ω SInt
     SAdd   : aexp Ω SInt → aexp Ω SInt → aexp Ω SInt
     SLam   : ∀ {γ₁ γ₂}   → aexp (γ₁ ∷ Ω) γ₂ → aexp Ω (SFun γ₁ γ₂)
     SApp   : ∀ {γ₁ γ₂}   → aexp Ω (SFun γ₁ γ₂) → aexp Ω γ₁ → aexp Ω γ₂
     DInt   : ℕ → aexp Ω (D Int)
     DAdd   : aexp Ω (D Int) → aexp Ω (D Int) → aexp Ω (D Int)
     DLam   : ∀ {τ₁ τ₂}   → aexp ((D τ₁) ∷ Ω) (D τ₂) → aexp Ω (D (Fun τ₁ τ₂))
     DApp   : ∀ {τ₁ τ₂}   → aexp Ω (D (Fun τ₁ τ₂)) → aexp Ω (D τ₁) → aexp Ω (D τ₂)
  -- Static pairs and sums
     _,_    : ∀ {γ₁ γ₂} → aexp Ω γ₁ → aexp Ω γ₂ → aexp Ω (γ₁ • γ₂)
     STl    : ∀ {γ₁ γ₂} → aexp Ω γ₁ → aexp Ω (γ₁ ⊎ γ₂)
     STr    : ∀ {γ₁ γ₂} → aexp Ω γ₂ → aexp Ω (γ₁ ⊎ γ₂)
     SFst   : ∀ {γ₁ γ₂} → aexp Ω (γ₁ • γ₂) → aexp Ω γ₁
     SSnd   : ∀ {γ₁ γ₂} → aexp Ω (γ₁ • γ₂) → aexp Ω γ₂
     SCase  : ∀ {γ₁ γ₂ γ₃} → aexp Ω (γ₁ ⊎ γ₂) → aexp (γ₁ ∷ Ω) γ₃ → aexp (γ₂ ∷ Ω) γ₃ → aexp Ω γ₃
  -- Dynamic pairs and sums
     _ḋ_    : ∀ {τ₁ τ₂} → aexp Ω (D τ₁) → aexp Ω (D τ₂) → aexp Ω (D (τ₁ • τ₂))
     DTl    : ∀ {τ₁ τ₂} → aexp Ω (D τ₁) → aexp Ω (D (τ₁ ⊎ τ₂))
     DTr    : ∀ {τ₁ τ₂} → aexp Ω (D τ₂) → aexp Ω (D (τ₁ ⊎ τ₂))
     DFst   : ∀ {τ₁ τ₂} → aexp Ω (D (τ₁ • τ₂)) → aexp Ω (D τ₁)
     DSnd   : ∀ {τ₁ τ₂} → aexp Ω (D (τ₁ • τ₂)) → aexp Ω (D τ₂)
     DCase  : ∀ {τ₁ τ₂ τ₃} → aexp Ω (D (τ₁ ⊎ τ₂)) → aexp ((D τ₁) ∷ Ω) (D τ₃) → aexp ((D τ₂) ∷ Ω) (D τ₃) → aexp Ω (D τ₃) 
  -- Liftable static terms
     Lift   : ∀ {γ} → Liftok γ → aexp Ω γ  → aexp Ω (D (typeof γ))

   ---------------------------------------------------------------
   --Isomorphism between terms typed by [AExp] and terms by [aexp]
   ---------------------------------------------------------------   
   module isomorphism where
   open import Data.Product
   open import Relation.Binary.PropositionalEquality
   ----------
   --Analysis
   ----------
   --consider static integer in [aexp],
   --SInt 0 : aexp Ω SInt,∀ Ω
   --naturally its counter-part in [AExp] should be,
   --AInt S 0 : AExp Δ (an S BInt)
   
   --for dynamic integer,
   --DInt 0 : aexp Ω (D Int)
   --AInt D 0 : aexp Δ (an D BInt)
   
   --Notice the two kinds of isomorphisms involved in above example
   --a. isomorphism w.r.t. types
   --b. isomorphism w.r.t. typed terms
   
   --------------------- 
   --a. type isomorphism
   ---------------------

   --a.1. [atype] to [AType]
   --integer
   --SInt ==> an S BInt
   --D Int ==> an D BInt 
   --function
   --SFun (D Int)(D Int) ==> an S (BFun (an D BInt) (an D BInt))
   --D (Fun Int Int) ==> an D (BFun (an D BInt) (an D BInt))
   
   ------------------------------------
   --projection from [atype] to [AType]
   ------------------------------------
   projT₁ : atype → AType 
   projT₁ SInt = an S BInt
   projT₁ (SFun aty aty₁) = an S (BFun (projT₁ aty) (projT₁ aty₁))
   projT₁ (D Int) = an D BInt
   projT₁ (D (Fun x x₁)) = an D (BFun (projT₁ (D x)) (projT₁ (D x₁)))
   projT₁ (D (x • x₁)) = an D (projT₁ (D x) • projT₁ (D x₁))
   projT₁ (D (x ⊎ x₁)) = an D (projT₁ (D x) ⊎ projT₁ (D x₁))
   projT₁ (aty • aty₁) = an S ((projT₁ aty) • projT₁ aty₁)
   projT₁ (aty ⊎ aty₁) = an S ((projT₁ aty) ⊎ projT₁ aty₁)
  
   --a.2. [AType] to [atype]
   --imposing [wft] upon types defined in [AType] before projection
   --consider the following type, 
   --an D (BFun (an S BInt) (an S BInt)) which has no counter part
   --in [atype] for the following lemma,
   --                ∀ γ, wft (projT₁ γ)
   --suppose we focus on these types satisfying [wft],
   --integer
   --an S BInt ==> SInt 
   --an D BInt ==> D Int
   --function
   --an S BFun (an D BInt) (an D BInt) ==> SFun (D Int) (D Int) 
   --an D BFun (an D BInt) (an D BInt) ==> D (Fun Int Int)
   
   ------------------------------------------------
   --projection from well-formed [AType] to [atype]
   ------------------------------------------------
   --------
   --helper
   --------
   ------------------------
   --from [atype] to [type]
   ------------------------
   γ→τ : atype → type
   γ→τ SInt = Int
   γ→τ (SFun aty aty₁) = Fun (γ→τ aty) (γ→τ aty₁)
   γ→τ (D x) = x
   γ→τ (aty • aty₁) = (γ→τ aty) • (γ→τ aty₁)
   γ→τ (aty ⊎ aty₁) = (γ→τ aty) ⊎ (γ→τ aty₁)

   
   projT₂ : (α : AType) → wft α → atype
   projT₂ .(an S BInt) (wf-int {S}) = SInt
   projT₂ .(an D BInt) (wf-int {D}) = D Int
   projT₂ .(an S (BFun α₁ α₂)) (wf-fun {S} {α₁} {α₂} wft wft₁ x x₁) = SFun (projT₂ α₁ wft) (projT₂ α₂ wft₁)
   projT₂ .(an D (BFun α₁ α₂)) (wf-fun {D} {α₁} {α₂} wft wft₁ x x₁) = D (Fun (γ→τ (projT₂ α₁ wft)) (γ→τ (projT₂ α₂ wft₁)))
   projT₂ .(an S (α₁ • α₂)) (wf-pair {S} {α₁} {α₂} wft wft₁ x x₁) = (projT₂ α₁ wft) • (projT₂ α₂ wft₁)
   projT₂ .(an D (α₁ • α₂)) (wf-pair {D} {α₁} {α₂} wft wft₁ x x₁) = D (γ→τ (projT₂ α₁ wft) • γ→τ (projT₂ α₂ wft₁))
   projT₂ .(an S (α₁ ⊎ α₂)) (wf-sum {S} {α₁} {α₂} wft wft₁ x x₁) = (projT₂ α₁ wft) ⊎ (projT₂ α₂ wft₁)
   projT₂ .(an D (α₁ ⊎ α₂)) (wf-sum {D} {α₁} {α₂} wft wft₁ x x₁) = D (γ→τ (projT₂ α₁ wft) ⊎ γ→τ (projT₂ α₂ wft₁))

   -------------------------------------
   --lemmas w.r.t. isomorphism of types
   -------------------------------------
   -----------------------------------------------
   --direction one:"starting from type in [atype]"
   -----------------------------------------------
   -----------------------
   --some auxiliary lemmas
   -----------------------
   S⊑* : ∀ {α} → S ⊑ btof α
   S⊑* {an S x₁} = reflS
   S⊑* {an D x₁} = S≤D
  
   a-pDatype : ∀ {τ : type} → btof (projT₁ (D τ)) ≡ D
   a-pDatype {Int} = refl
   a-pDatype {Fun τ τ₁} = refl
   a-pDatype {τ • τ₁} = refl
   a-pDatype {τ ⊎ τ₁} = refl

   D-a-pDatype : ∀ {τ : type} → D ⊑ (btof (projT₁ (D τ)))
   D-a-pDatype {τ} rewrite a-pDatype {τ} = reflD
   
   isoT₁ : ∀ (γ : atype) → Σ (wft (projT₁ γ)) \ x → γ ≡ projT₂ (projT₁ γ) x  
   isoT₁ SInt = wf-int , refl
   isoT₁ (SFun γ γ₁)  with (proj₂ (isoT₁ γ)) | (proj₂ (isoT₁ γ₁))
   ... | I | I' = wf-fun (proj₁ (isoT₁ γ)) (proj₁ (isoT₁ γ₁)) (S⊑* {(projT₁ γ)}) (S⊑* {projT₁ γ₁}) , cong₂ SFun I I'
   isoT₁ (D Int) = wf-int , refl
   isoT₁ (D (Fun x x₁)) = wf-fun (proj₁ (isoT₁ (D x))) (proj₁ (isoT₁ (D x₁))) (D-a-pDatype {x}) (D-a-pDatype {x₁}) ,
                                  cong 
                                    D
                                  (cong₂ Fun (cong γ→τ (proj₂ (isoT₁ (D x))))
                                  (cong γ→τ (proj₂ (isoT₁ (D x₁)))))
   isoT₁ (D (x • x₁)) = wf-pair (proj₁ (isoT₁ (D x))) (proj₁ (isoT₁ (D x₁))) (D-a-pDatype {x}) (D-a-pDatype {x₁}) , 
                                  cong 
                                    D
                                  (cong₂ _•_ (cong γ→τ (proj₂ (isoT₁ (D x))))
                                  (cong γ→τ (proj₂ (isoT₁ (D x₁)))))
   isoT₁ (D (x ⊎ x₁)) = wf-sum (proj₁ (isoT₁ (D x))) (proj₁ (isoT₁ (D x₁))) (D-a-pDatype {x}) (D-a-pDatype {x₁}) ,
                                  cong 
                                    D
                                  (cong₂ _⊎_ (cong γ→τ (proj₂ (isoT₁ (D x))))
                                  (cong γ→τ (proj₂ (isoT₁ (D x₁)))))
   isoT₁ (γ • γ₁) = wf-pair (proj₁ (isoT₁ γ)) (proj₁ (isoT₁ γ₁)) (S⊑* {projT₁ γ}) (S⊑* {projT₁ γ₁}) , 
                             cong₂ _•_ (proj₂ (isoT₁ γ)) (proj₂ (isoT₁ γ₁))
   isoT₁ (γ ⊎ γ₁) = wf-sum (proj₁ (isoT₁ γ)) (proj₁ (isoT₁ γ₁)) (S⊑* {projT₁ γ}) (S⊑* {projT₁ γ₁}) , 
                             cong₂ _⊎_ (proj₂ (isoT₁ γ)) (proj₂ (isoT₁ γ₁))

  
   -----------------------------------------------------------
   --direction two:"starting from type in well-formed [AType]"
   -----------------------------------------------------------
   -----------------------
   --some auxiliary lemmas
   -----------------------
   eqDγ→τprojT₂ : ∀ {α : AType} {wf : wft α} → D ⊑ btof α → D (γ→τ (projT₂ α wf)) ≡ projT₂ α wf
   eqDγ→τprojT₂ {an S BInt} {wf-int} ()
   eqDγ→τprojT₂ {an D BInt} {wf-int} e = refl
   eqDγ→τprojT₂ {an S (BFun α₁ α₂)} {wf-fun wf wf₁ x x₁} ()
   eqDγ→τprojT₂ {an D (BFun α₁ α₂)} {wf-fun wf wf₁ x x₁} e = refl
   eqDγ→τprojT₂ {an S (α₁ • α₂)} {wf-pair wf wf₁ x x₁} ()
   eqDγ→τprojT₂ {an D (α₁ • α₂)} {wf-pair wf wf₁ x x₁} e = refl
   eqDγ→τprojT₂ {an S (α₁ ⊎ α₂)} {wf-sum wf wf₁ x x₁} ()
   eqDγ→τprojT₂ {an D (α₁ ⊎ α₂)} {wf-sum wf wf₁ x x₁} e = refl

   
  
   isoT₂ : ∀ {α : AType} → (wf : wft α) → α ≡  projT₁ (projT₂ α wf)
   isoT₂ {an S BInt} wf-int = refl
   isoT₂ {an S (BFun x x₁)} (wf-fun wf wf₁ x₂ x₃) = cong₂ an refl (cong₂ BFun (isoT₂ {x} wf) (isoT₂ {x₁} wf₁))
   isoT₂ {an S (x • x₁)} (wf-pair wf wf₁ x₂ x₃) = cong₂ an refl (cong₂ _•_ (isoT₂ {x} wf) (isoT₂ {x₁} wf₁))
   isoT₂ {an S (x ⊎ x₁)} (wf-sum wf wf₁ x₂ x₃) = cong₂ an refl (cong₂ _⊎_ (isoT₂ {x} wf) (isoT₂ {x₁} wf₁))
   isoT₂ {an D BInt} wf-int = refl
   isoT₂ {an D (BFun x x₁)} (wf-fun wf wf₁ x₂ x₃) = 
       cong₂ an refl
         (cong₂ BFun
          (trans (isoT₂ {x} wf)
           (sym (cong projT₁ (eqDγ→τprojT₂ {x} {wf} x₂))))
          (trans (isoT₂ {x₁} wf₁)
           (sym (cong projT₁ (eqDγ→τprojT₂ {x₁} {wf₁} x₃)))))
   isoT₂ {an D (x • x₁)} (wf-pair wf wf₁ x₂ x₃) = 
         cong₂ an refl
           (cong₂ _•_
            (trans (isoT₂ {x} wf)
             (sym (cong projT₁ (eqDγ→τprojT₂ {x} {wf} x₂))))
            (trans (isoT₂ {x₁} wf₁)
             (sym (cong projT₁ (eqDγ→τprojT₂ {x₁} {wf₁} x₃)))))
   isoT₂ {an D (x ⊎ x₁)} (wf-sum wf wf₁ x₂ x₃) = 
         cong₂ an refl
           (cong₂ _⊎_
            (trans (isoT₂ {x} wf)
             (sym (cong projT₁ (eqDγ→τprojT₂ {x} {wf} x₂))))
            (trans (isoT₂ {x₁} wf₁)
             (sym (cong projT₁ (eqDγ→τprojT₂ {x₁} {wf₁} x₃))))) 
  
   
   ------------------------------------------------
   --lemmas w.r.t. isomorphism of typed expressions
   ------------------------------------------------
   ----------------
   --some instances
   ----------------
   ------------------
   --[AExp] to [aexp]
   ------------------
   --Var hd : AExp [an D (BFun (an D BInt) (an D BInt))] 
   --               (an D (BFun (an D BInt) (an D BInt)))
   --==>projt₂* 
   --Var hd : aexp [D (Fun Int Int)] (D (Fun Int Int))
   --*Note that projection from expression in [AExp] to
   -- that in [aexp] requires that both the type and the 
   -- typing environment are well-formed
   
   --AInt S 0 : AExp Δ (an S BInt),∀ Δ
   --==>projt₂
   --SInt 0 : aexp Ω* SInt,∀ Ω
   --*Note that the corresponding typing environment in [aexp] satisfies,
   -- Ω = projection of Δ

   --ALam S (wf-fun wf-int wf-int *≤D *≤D) (Var hd) 
   --:AExp [] (an S (BFun (an D BInt) (an D BInt)))
   --==>projt₂
   --SLam (Var hd) : aexp [] (SFun (D Int) (D Int))
   --ALam D (wf-fun wf-int wf-int refl refl) (Var hd)
   --:AExp [] (an D (BFun (an D BInt) (an D BInt)))
   --==>projt₂
   --DLam (Var hd) : aexp [] (D (Fun Int Int))
   
   -----------------------
   --summary upon [projt₂]
   -----------------------
   --• projection only of terms which are typed both by
   --  well-formed [AType] and under well-formed Δ
   --• the results are typed under Ω which is the projection
   --  of Δ
   ------------------------------------------
   --some auxiliary functions and definitions
   ------------------------------------------
   ---------------
   --Well-formed Δ
   ---------------
   data wfe : ACtx → Set where
     wf-[]  : wfe []
     wf-∷   : ∀ {α : AType} {AEnv : ACtx}  
                 → wft α → wfe AEnv
                 → wfe (α ∷ AEnv)
   
   -----------------------------
   --projΔ (similar to [projT₂])
   -----------------------------
   projΔ : (Δ : ACtx) → wfe Δ → actx
   projΔ [] wfe = []
   projΔ (x ∷ Δ) (wf-∷ x₁ wfe) = projT₂ x x₁ ∷ projΔ Δ wfe
   
   --------
   --projt₂
   --------
   -----------------------
   --some auxiliary lemmas
   -----------------------
   -- --------
   -- --is-≡-α
   -- --------
   -- is-≡-α : (α₁ α₂ : AType) → Bool
   -- is-≡-α (an S BInt) (an S BInt) = true
   -- is-≡-α (an S BInt) (an S (BFun x x₁)) = false
   -- is-≡-α (an S BInt) (an S (x • x₁)) = false
   -- is-≡-α (an S BInt) (an S (x ⊎ x₁)) = false
   -- is-≡-α (an S (BFun x x₁)) (an S BInt) = false
   -- is-≡-α (an S (BFun x x₁)) (an S (BFun x₂ x₃)) = is-≡-α x x₂ ∧ is-≡-α x₁ x₃
   -- is-≡-α (an S (BFun x x₁)) (an S (x₂ • x₃)) = false
   -- is-≡-α (an S (BFun x x₁)) (an S (x₂ ⊎ x₃)) = false
   -- is-≡-α (an S (x • x₁)) (an S BInt) = false
   -- is-≡-α (an S (x • x₁)) (an S (BFun x₂ x₃)) = false
   -- is-≡-α (an S (x • x₁)) (an S (x₂ • x₃)) = is-≡-α x x₂ ∧ is-≡-α x₁ x₃
   -- is-≡-α (an S (x • x₁)) (an S (x₂ ⊎ x₃)) = false
   -- is-≡-α (an S (x ⊎ x₁)) (an S BInt) = false
   -- is-≡-α (an S (x ⊎ x₁)) (an S (BFun x₂ x₃)) = false
   -- is-≡-α (an S (x ⊎ x₁)) (an S (x₂ • x₃)) = false
   -- is-≡-α (an S (x ⊎ x₁)) (an S (x₂ ⊎ x₃)) = is-≡-α x x₂ ∧ is-≡-α x₁ x₃
   -- is-≡-α (an S x₁) (an D x₃) = false
   -- is-≡-α (an D x₁) (an S x₃) = false
   -- is-≡-α (an D BInt) (an D BInt) = true
   -- is-≡-α (an D BInt) (an D (BFun x x₁)) = false
   -- is-≡-α (an D BInt) (an D (x • x₁)) = false
   -- is-≡-α (an D BInt) (an D (x ⊎ x₁)) = false
   -- is-≡-α (an D (BFun x x₁)) (an D BInt) = false
   -- is-≡-α (an D (BFun x x₁)) (an D (BFun x₂ x₃)) = is-≡-α x x₂ ∧ is-≡-α x₁ x₃
   -- is-≡-α (an D (BFun x x₁)) (an D (x₂ • x₃)) = false
   -- is-≡-α (an D (BFun x x₁)) (an D (x₂ ⊎ x₃)) = false
   -- is-≡-α (an D (x • x₁)) (an D BInt) = false
   -- is-≡-α (an D (x • x₁)) (an D (BFun x₂ x₃)) = false
   -- is-≡-α (an D (x • x₁)) (an D (x₂ • x₃)) = is-≡-α x x₂ ∧ is-≡-α x₁ x₃
   -- is-≡-α (an D (x • x₁)) (an D (x₂ ⊎ x₃)) = false
   -- is-≡-α (an D (x ⊎ x₁)) (an D BInt) = false
   -- is-≡-α (an D (x ⊎ x₁)) (an D (BFun x₂ x₃)) = false
   -- is-≡-α (an D (x ⊎ x₁)) (an D (x₂ • x₃)) = false
   -- is-≡-α (an D (x ⊎ x₁)) (an D (x₂ ⊎ x₃)) = is-≡-α x x₂ ∧ is-≡-α x₁ x₃

   -- --------
   -- --is-≡-τ
   -- --------
   -- is-≡-τ : (τ₁ τ₂ : type) → Bool
   -- is-≡-τ Int Int = true
   -- is-≡-τ Int (Fun τ₂ τ₃) = false
   -- is-≡-τ Int (τ₂ • τ₃) = false
   -- is-≡-τ Int (τ₂ ⊎ τ₃) = false
   -- is-≡-τ (Fun τ₁ τ₂) Int = false
   -- is-≡-τ (Fun τ₁ τ₂) (Fun τ₃ τ₄) = is-≡-τ τ₁ τ₃ ∧ is-≡-τ τ₂ τ₄
   -- is-≡-τ (Fun τ₁ τ₂) (τ₃ • τ₄) = false
   -- is-≡-τ (Fun τ₁ τ₂) (τ₃ ⊎ τ₄) = false
   -- is-≡-τ (τ₁ • τ₂) Int = false
   -- is-≡-τ (τ₁ • τ₂) (Fun τ₃ τ₄) = false
   -- is-≡-τ (τ₁ • τ₂) (τ₃ • τ₄) = is-≡-τ τ₁ τ₃ ∧ is-≡-τ τ₂ τ₄
   -- is-≡-τ (τ₁ • τ₂) (τ₃ ⊎ τ₄) = false
   -- is-≡-τ (τ₁ ⊎ τ₂) Int = false
   -- is-≡-τ (τ₁ ⊎ τ₂) (Fun τ₃ τ₄) = false
   -- is-≡-τ (τ₁ ⊎ τ₂) (τ₃ • τ₄) = false
   -- is-≡-τ (τ₁ ⊎ τ₂) (τ₃ ⊎ τ₄) = is-≡-τ τ₁ τ₃ ∧ is-≡-τ τ₂ τ₄
   -- --------
   -- --is-≡-γ
   -- --------
   -- is-≡-γ : (γ₁ γ₂ : atype) → Bool
   -- is-≡-γ SInt SInt = true
   -- is-≡-γ SInt (SFun γ₂ γ₃) = false
   -- is-≡-γ SInt (D x) = false
   -- is-≡-γ SInt (γ₂ • γ₃) = false
   -- is-≡-γ SInt (γ₂ ⊎ γ₃) = false
   -- is-≡-γ (SFun γ₁ γ₂) SInt = false
   -- is-≡-γ (SFun γ₁ γ₂) (SFun γ₃ γ₄) = is-≡-γ γ₁ γ₃ ∧ is-≡-γ γ₂ γ₄
   -- is-≡-γ (SFun γ₁ γ₂) (D x) = false
   -- is-≡-γ (SFun γ₁ γ₂) (γ₃ • γ₄) = false
   -- is-≡-γ (SFun γ₁ γ₂) (γ₃ ⊎ γ₄) = false
   -- is-≡-γ (D x) SInt = false
   -- is-≡-γ (D x) (SFun γ₂ γ₃) = false
   -- is-≡-γ (D x) (D x₁) = is-≡-τ x x₁
   -- is-≡-γ (D x) (γ₂ • γ₃) = false
   -- is-≡-γ (D x) (γ₂ ⊎ γ₃) = false
   -- is-≡-γ (γ₁ • γ₂) SInt = false
   -- is-≡-γ (γ₁ • γ₂) (SFun γ₃ γ₄) = false
   -- is-≡-γ (γ₁ • γ₂) (D x) = false
   -- is-≡-γ (γ₁ • γ₂) (γ₃ • γ₄) = is-≡-γ γ₁ γ₃ ∧ is-≡-γ γ₂ γ₄
   -- is-≡-γ (γ₁ • γ₂) (γ₃ ⊎ γ₄) = false
   -- is-≡-γ (γ₁ ⊎ γ₂) SInt = false
   -- is-≡-γ (γ₁ ⊎ γ₂) (SFun γ₃ γ₄) = false
   -- is-≡-γ (γ₁ ⊎ γ₂) (D x) = false
   -- is-≡-γ (γ₁ ⊎ γ₂) (γ₃ • γ₄) = false
   -- is-≡-γ (γ₁ ⊎ γ₂) (γ₃ ⊎ γ₄) = is-≡-γ γ₁ γ₃ ∧ is-≡-γ γ₂ γ₄

   -- is-≡-γ→τ : {γ₁ γ₂ : atype} → btof-γ γ₁ ≡ D → btof-γ γ₁ ≡ btof-γ γ₂ 
   --             → is-≡-γ γ₁ γ₂ ≡ is-≡-τ (γ→τ γ₁) (γ→τ γ₂)
   -- is-≡-γ→τ {SInt} {SInt} eq eq' = refl
   -- is-≡-γ→τ {SInt} {SFun γ₂ γ₃} eq eq' = refl
   -- is-≡-γ→τ {SInt} {D x} () () 
   -- is-≡-γ→τ {SInt} {γ₂ • γ₃} () eq'
   -- is-≡-γ→τ {SInt} {γ₂ ⊎ γ₃} () eq'
   -- is-≡-γ→τ {SFun γ₁ γ₂} {SInt} () eq'
   -- is-≡-γ→τ {SFun γ₁ γ₂} {SFun γ₃ γ₄} () eq'
   -- is-≡-γ→τ {SFun γ₁ γ₂} {D x} () eq'
   -- is-≡-γ→τ {SFun γ₁ γ₂} {γ₃ • γ₄} () eq'
   -- is-≡-γ→τ {SFun γ₁ γ₂} {γ₃ ⊎ γ₄} () eq'
   -- is-≡-γ→τ {D x} {SInt} eq ()
   -- is-≡-γ→τ {D x} {SFun γ₂ γ₃} eq ()
   -- is-≡-γ→τ {D x} {D x₁} eq eq' = refl
   -- is-≡-γ→τ {D x} {γ₂ • γ₃} eq ()
   -- is-≡-γ→τ {D x} {γ₂ ⊎ γ₃} eq ()
   -- is-≡-γ→τ {γ₁ • γ₂} {SInt} eq eq' = refl
   -- is-≡-γ→τ {γ₁ • γ₂} {SFun γ₃ γ₄} () eq'
   -- is-≡-γ→τ {γ₁ • γ₂} {D x} eq ()
   -- is-≡-γ→τ {γ₁ • γ₂} {γ₃ • γ₄} () eq'
   -- is-≡-γ→τ {γ₁ • γ₂} {γ₃ ⊎ γ₄} () eq'
   -- is-≡-γ→τ {γ₁ ⊎ γ₂} {SInt} () eq'
   -- is-≡-γ→τ {γ₁ ⊎ γ₂} {SFun γ₃ γ₄} () eq'
   -- is-≡-γ→τ {γ₁ ⊎ γ₂} {D x} eq ()
   -- is-≡-γ→τ {γ₁ ⊎ γ₂} {γ₃ • γ₄} () eq'
   -- is-≡-γ→τ {γ₁ ⊎ γ₂} {γ₃ ⊎ γ₄} () eq'

   -- btof-γ-projT₂-α : ∀ {a : BT} {σ : BType} {wft : wft (an a σ)}
   --                     → btof-γ (projT₂ (an a σ) wft) ≡ a
   -- btof-γ-projT₂-α {S} {BInt} {wf-int} = refl
   -- btof-γ-projT₂-α {D} {BInt} {wf-int} = refl
   -- btof-γ-projT₂-α {S} {BFun α₁ α₂} {wf-fun wft wft₁ x x₁} = refl
   -- btof-γ-projT₂-α {D} {BFun α₁ α₂} {wf-fun wft wft₁ x x₁} = refl
   -- btof-γ-projT₂-α {S} {α₁ • α₂} {wf-pair wft wft₁ x x₁} = refl
   -- btof-γ-projT₂-α {D} {α₁ • α₂} {wf-pair wft wft₁ x x₁} = refl
   -- btof-γ-projT₂-α {S} {α₁ ⊎ α₂} {wf-sum wft wft₁ x x₁} = refl
   -- btof-γ-projT₂-α {D} {α₁ ⊎ α₂} {wf-sum wft wft₁ x x₁} = refl
   

  
   -- is-≡-projT₂ : {α₁ α₂ : AType} {wft₁ : wft α₁} {wft₂ : wft α₂}
   --                → (is-≡-α α₁ α₂) ≡ (is-≡-γ (projT₂ α₁ wft₁) (projT₂ α₂ wft₂)) 
   -- is-≡-projT₂ {an S BInt} {an S BInt} {wf-int} {wf-int} = refl
   -- is-≡-projT₂ {an S BInt} {an D BInt} {wf-int} {wf-int} = refl
   -- is-≡-projT₂ {an D BInt} {an S BInt} {wf-int} {wf-int} = refl
   -- is-≡-projT₂ {an D BInt} {an D BInt} {wf-int} {wf-int} = refl
   -- is-≡-projT₂ {an S BInt} {an S (BFun α₁ α₂)} {wf-int} {wf-fun wft₂ wft₃ x x₁} = refl
   -- is-≡-projT₂ {an S BInt} {an D (BFun α₁ α₂)} {wf-int} {wf-fun wft₂ wft₃ x x₁} = refl
   -- is-≡-projT₂ {an D BInt} {an S (BFun α₁ α₂)} {wf-int} {wf-fun wft₂ wft₃ x x₁} = refl
   -- is-≡-projT₂ {an D BInt} {an D (BFun α₁ α₂)} {wf-int} {wf-fun wft₂ wft₃ x x₁} = refl
   -- is-≡-projT₂ {an S BInt} {an S (α₁ • α₂)} {wf-int} {wf-pair wft₂ wft₃ x x₁} = refl
   -- is-≡-projT₂ {an S BInt} {an D (α₁ • α₂)} {wf-int} {wf-pair wft₂ wft₃ x x₁} = refl
   -- is-≡-projT₂ {an D BInt} {an S (α₁ • α₂)} {wf-int} {wf-pair wft₂ wft₃ x x₁} = refl
   -- is-≡-projT₂ {an D BInt} {an D (α₁ • α₂)} {wf-int} {wf-pair wft₂ wft₃ x x₁} = refl
   -- is-≡-projT₂ {an S BInt} {an S (α₁ ⊎ α₂)} {wf-int} {wf-sum wft₂ wft₃ x x₁} = refl
   -- is-≡-projT₂ {an S BInt} {an D (α₁ ⊎ α₂)} {wf-int} {wf-sum wft₂ wft₃ x x₁} = refl
   -- is-≡-projT₂ {an D BInt} {an S (α₁ ⊎ α₂)} {wf-int} {wf-sum wft₂ wft₃ x x₁} = refl
   -- is-≡-projT₂ {an D BInt} {an D (α₁ ⊎ α₂)} {wf-int} {wf-sum wft₂ wft₃ x x₁} = refl
   -- is-≡-projT₂ {an S (BFun α₁ α₃)} {an S BInt} {wf-fun wft₁ wft₂ x x₁} {wf-int} = refl
   -- is-≡-projT₂ {an S (BFun α₁ α₃)} {an D BInt} {wf-fun wft₁ wft₂ x x₁} {wf-int} = refl
   -- is-≡-projT₂ {an D (BFun α₁ α₃)} {an S BInt} {wf-fun wft₁ wft₂ x x₁} {wf-int} = refl
   -- is-≡-projT₂ {an D (BFun α₁ α₃)} {an D BInt} {wf-fun wft₁ wft₂ x x₁} {wf-int} = refl
   -- is-≡-projT₂ {an S (BFun α₁ α₃)} {an S (BFun α₂ α₄)} {wf-fun wft₁ wft₂ x x₁} {wf-fun wft₃ wft₄ x₂ x₃} 
   --    rewrite (is-≡-projT₂ {α₁} {α₂} {wft₁} {wft₃}) | (is-≡-projT₂ {α₃} {α₄} {wft₂} {wft₄}) = refl
   -- is-≡-projT₂ {an S (BFun α₁ α₃)} {an D (BFun α₂ α₄)} {wf-fun wft₁ wft₂ x x₁} {wf-fun wft₃ wft₄ x₂ x₃} = refl
   -- is-≡-projT₂ {an D (BFun α₁ α₃)} {an S (BFun α₂ α₄)} {wf-fun wft₁ wft₂ x x₁} {wf-fun wft₃ wft₄ x₂ x₃} = refl
   -- is-≡-projT₂ {an D (BFun (an D σ₁) (an D σ₃))} {an D (BFun (an D σ₂) (an D σ₄))} {wf-fun wft₁ wft₂ x x₁} {wf-fun wft₃ wft₄ x₂ x₃}
   --    rewrite ((is-≡-projT₂ {an D σ₁} {an D σ₂} {wft₁} {wft₃})) | ((is-≡-projT₂ {an D σ₃} {an D σ₄} {wft₂} {wft₄})) 
   --            | is-≡-γ→τ {projT₂ (an D σ₁) wft₁} {projT₂ (an D σ₂) wft₃} 
   --              (btof-γ-projT₂-α {D} {σ₁} {wft₁}) (trans (btof-γ-projT₂-α {D} {σ₁} {wft₁}) (sym (btof-γ-projT₂-α {D} {σ₂} {wft₃})))
   --            | is-≡-γ→τ {projT₂ (an D σ₃) wft₂} {projT₂ (an D σ₄) wft₄} 
   --              (btof-γ-projT₂-α {D} {σ₃} {wft₂}) (trans (btof-γ-projT₂-α {D} {σ₃} {wft₂}) (sym (btof-γ-projT₂-α {D} {σ₄} {wft₄})))
   --    = refl
   -- is-≡-projT₂ {an D (BFun (an D σ₁) (an D σ₃))} {an D (BFun (an D σ₂) (an S σ₄))} {wf-fun wft₁ wft₂ x x₁} {wf-fun wft₃ wft₄ x₂ ()}
   -- is-≡-projT₂ {an D (BFun (an D σ₁) (an S σ₃))} {an D (BFun (an D σ₂) (an a₄ σ₄))} {wf-fun wft₁ wft₂ x ()} {wf-fun wft₃ wft₄ x₂ x₃}
   -- is-≡-projT₂ {an D (BFun (an D σ₁) (an a₃ σ₃))} {an D (BFun (an S σ₂) (an a₄ σ₄))} {wf-fun wft₁ wft₂ x x₁}  {wf-fun wft₃ wft₄ () x₃}
   -- is-≡-projT₂ {an D (BFun (an S σ₁) (an a₃ σ₃))} {an D (BFun (an D σ₂) (an a₄ σ₄))} {wf-fun wft₁ wft₂ () x₁} {wf-fun wft₃ wft₄ x₂ x₃} 
   -- is-≡-projT₂ {an D (BFun (an S σ₁) (an a₃ σ₃))} {an D (BFun (an S σ₂) (an a₄ σ₄))} {wf-fun wft₁ wft₂ () x₁} {wf-fun wft₃ wft₄ () x₃}
   -- is-≡-projT₂ {an S (BFun α₁ α₃)} {an S (α₂ • α₄)} {wf-fun wft₁ wft₂ x x₁} {wf-pair wft₃ wft₄ x₂ x₃} = refl
   -- is-≡-projT₂ {an S (BFun α₁ α₃)} {an D (α₂ • α₄)} {wf-fun wft₁ wft₂ x x₁} {wf-pair wft₃ wft₄ x₂ x₃} = refl
   -- is-≡-projT₂ {an D (BFun α₁ α₃)} {an S (α₂ • α₄)} {wf-fun wft₁ wft₂ x x₁} {wf-pair wft₃ wft₄ x₂ x₃} = refl
   -- is-≡-projT₂ {an D (BFun α₁ α₃)} {an D (α₂ • α₄)} {wf-fun wft₁ wft₂ x x₁} {wf-pair wft₃ wft₄ x₂ x₃} = refl
   -- is-≡-projT₂ {an S (BFun α₁ α₃)} {an S (α₂ ⊎ α₄)} {wf-fun wft₁ wft₂ x x₁} {wf-sum wft₃ wft₄ x₂ x₃} = refl
   -- is-≡-projT₂ {an S (BFun α₁ α₃)} {an D (α₂ ⊎ α₄)} {wf-fun wft₁ wft₂ x x₁} {wf-sum wft₃ wft₄ x₂ x₃} = refl
   -- is-≡-projT₂ {an D (BFun α₁ α₃)} {an S (α₂ ⊎ α₄)} {wf-fun wft₁ wft₂ x x₁} {wf-sum wft₃ wft₄ x₂ x₃} = refl
   -- is-≡-projT₂ {an D (BFun α₁ α₃)} {an D (α₂ ⊎ α₄)} {wf-fun wft₁ wft₂ x x₁} {wf-sum wft₃ wft₄ x₂ x₃} = refl
   -- is-≡-projT₂ {an S (α₁ • α₃)} {an S BInt} {wf-pair wft₁ wft₂ x x₁} {wf-int} = refl
   -- is-≡-projT₂ {an S (α₁ • α₃)} {an D BInt} {wf-pair wft₁ wft₂ x x₁} {wf-int} = refl
   -- is-≡-projT₂ {an D (α₁ • α₃)} {an S BInt} {wf-pair wft₁ wft₂ x x₁} {wf-int} = refl
   -- is-≡-projT₂ {an D (α₁ • α₃)} {an D BInt} {wf-pair wft₁ wft₂ x x₁} {wf-int} = refl
   -- is-≡-projT₂ {an S (α₁ • α₃)} {an S (BFun α₂ α₄)} {wf-pair wft₁ wft₂ x x₁} {wf-fun wft₃ wft₄ x₂ x₃} = refl
   -- is-≡-projT₂ {an S (α₁ • α₃)} {an D (BFun α₂ α₄)} {wf-pair wft₁ wft₂ x x₁} {wf-fun wft₃ wft₄ x₂ x₃} = refl
   -- is-≡-projT₂ {an D (α₁ • α₃)} {an S (BFun α₂ α₄)} {wf-pair wft₁ wft₂ x x₁} {wf-fun wft₃ wft₄ x₂ x₃} = refl
   -- is-≡-projT₂ {an D (α₁ • α₃)} {an D (BFun α₂ α₄)} {wf-pair wft₁ wft₂ x x₁} {wf-fun wft₃ wft₄ x₂ x₃} = refl
   -- is-≡-projT₂ {an S (α₁ • α₃)} {an S (α₂ • α₄)} {wf-pair wft₁ wft₂ x x₁} {wf-pair wft₃ wft₄ x₂ x₃} 
   --   rewrite (is-≡-projT₂ {α₁} {α₂} {wft₁} {wft₃}) | (is-≡-projT₂ {α₃} {α₄} {wft₂} {wft₄})
   --   = refl
   -- is-≡-projT₂ {an S (α₁ • α₃)} {an D (α₂ • α₄)} {wf-pair wft₁ wft₂ x x₁} {wf-pair wft₃ wft₄ x₂ x₃} = refl
   -- is-≡-projT₂ {an D (α₁ • α₃)} {an S (α₂ • α₄)} {wf-pair wft₁ wft₂ x x₁} {wf-pair wft₃ wft₄ x₂ x₃} = refl
   -- is-≡-projT₂ {an D (α₁ • α₃)} {an D (α₂ • α₄)} {wf-pair wft₁ wft₂ x x₁} {wf-pair wft₃ wft₄ x₂ x₃} = {!!}
   -- is-≡-projT₂ {an a (α₁ • α₃)} {(an a₁ (α₂ ⊎ α₄))} {wf-pair wft₁ wft₂ x x₁} {wf-sum wft₃ wft₄ x₂ x₃} = {!!}
   -- is-≡-projT₂ {(an a (α₁ ⊎ α₃))} {α₂} {wf-sum wft₁ wft₂ x x₁} {wft'} = {!!}
   ⊑-≡ : ∀ {a b : BT} → (e : a ⊑ b) → (e' : a ⊑ b) → e ≡ e'
   ⊑-≡ {S} {S} reflS reflS = refl
   ⊑-≡ {S} {D} S≤D S≤D = refl
   ⊑-≡ {D} {S} () e'
   ⊑-≡ {D} {D} reflD reflD = refl


   wft-≡ : ∀ {α : AType} → (α₁ : wft α) → (α₂ : wft α) → α₁ ≡ α₂
   wft-≡ wf-int wf-int = refl
   wft-≡ (wf-fun wft₁ wft₂ x x₁) (wf-fun wft₃ wft₄ x₂ x₃) rewrite wft-≡ wft₁ wft₃ | wft-≡ wft₂ wft₄ | ⊑-≡ x x₂ | ⊑-≡ x₁ x₃ 
      = refl
   wft-≡ (wf-pair wft₁ wft₂ x x₁) (wf-pair wft₃ wft₄ x₂ x₃) rewrite wft-≡ wft₁ wft₃ | wft-≡ wft₂ wft₄ | ⊑-≡ x x₂ | ⊑-≡ x₁ x₃
      = refl
   wft-≡ (wf-sum wft₁ wft₂ x x₁) (wf-sum wft₃ wft₄ x₂ x₃) rewrite wft-≡ wft₁ wft₃ | wft-≡ wft₂ wft₄ | ⊑-≡ x x₂ | ⊑-≡ x₁ x₃
      = refl            

   id-projT₂&Δ :  {α : AType} {Δ : ACtx} 
                 → (wft : wft α) → (wfe : wfe Δ) 
                 → (id : α ∈ Δ)
                 →   projT₂ α wft ∈ (projΔ Δ wfe)
   id-projT₂&Δ {α} {[]} wft wfe ()
   id-projT₂&Δ {.x} {x ∷ Δ} wft (wf-∷ x₁ wfe) hd rewrite wft-≡ x₁ wft = hd {x = projT₂ x wft} {xs = projΔ Δ wfe}
   id-projT₂&Δ {α} {x ∷ Δ} wft (wf-∷ x₁ wfe) (tl x₂) = tl (id-projT₂&Δ wft wfe x₂)

   αAExp→wft : ∀ {α : AType} {Δ : ACtx} → (e : AExp Δ α) → wft α
   αAExp→wft {α} {Δ} e = {!!}

   projt₂ : ∀ {α : AType} {Δ : ACtx} → (wft : wft α) → (wfe : wfe Δ)
              → AExp Δ α → aexp (projΔ Δ wfe) (projT₂ α wft)
   projt₂ {an x x₁} wft wfe (Var x₂) = Var (id-projT₂&Δ wft wfe x₂)
   projt₂ {an S BInt} wf-int wfe (AInt .S x₁) = SInt x₁
   projt₂ {an D BInt} wf-int wfe (AInt .D x₁) = DInt x₁
   projt₂ {an S BInt} wf-int wfe (AAdd .S e e₁) = SAdd (projt₂ wf-int wfe e) (projt₂ wf-int wfe e₁)
   projt₂ {an D BInt} wf-int wfe (AAdd .D e e₁) = DAdd (projt₂ wf-int wfe e) (projt₂ wf-int wfe e₁)
   projt₂ {an S (BFun α₁ α₂)} {Δ} (wf-fun wft wft₁ x x₁) wfe (ALam .S x₂ e) = SLam (projt₂ {α₂} {α₁ ∷ Δ} wft₁ (wf-∷ wft wfe) e)
   projt₂ {an D (BFun α₁ α₂)} {Δ} (wf-fun wft wft₁ x x₁) wfe (ALam .D x₂ e) =
    DLam myrewrite
       where myrewrite :  aexp (D (γ→τ (projT₂ α₁ wft)) ∷ projΔ Δ wfe) (D (γ→τ (projT₂ α₂ wft₁)))
             myrewrite rewrite (cong₂ aexp (cong₂  (_∷_) {D (γ→τ (projT₂ α₁ wft))} {projT₂ α₁ wft} {projΔ Δ wfe} {projΔ Δ wfe} 
                               (eqDγ→τprojT₂ {α₁} {wft} x) refl) (eqDγ→τprojT₂ {α₂} {wft₁} x₁))
               = projt₂ {α₂} {α₁ ∷ Δ} wft₁ (wf-∷ wft wfe) e
     
   projt₂ {an x x₁} wft wfe (AApp {α₁} S (wf-fun x₂ x₃ x₄ x₅) e e₁) rewrite sym (wft-≡ x₃ wft)  
     = SApp {γ₁ = (projT₂ α₁ x₂)} (projt₂ (wf-fun x₂ x₃ x₄ x₅) wfe e) (projt₂ x₂ wfe e₁)
   projt₂ {an S x₁} wft wfe (AApp D (wf-fun x₂ x₃ x ()) e e₁)
   projt₂ {an D x₁} wft wfe (AApp {an S x₂} D (wf-fun x₃ x₄ () x₅) e e₁)
   projt₂ {an D x₁} {Δ} wft wfe (AApp {an D x₂} D (wf-fun x₃ x₄ x x₅) e e₁) 
     rewrite sym (wft-≡ x₄ wft)
       = myrewrite'
           where myrewrite' : aexp (projΔ Δ wfe) (projT₂ (an D x₁) x₄)
                 myrewrite' rewrite sym (cong₂ aexp {(projΔ Δ wfe)} {(projΔ Δ wfe)} refl (eqDγ→τprojT₂ {an D x₁} {x₄} x₅))
                       = DApp (projt₂ (wf-fun x₃ x₄ x x₅) wfe e) myrewrite
                                  where myrewrite : aexp (projΔ Δ wfe) (D (γ→τ (projT₂ (an D x₂) x₃)))
                                        myrewrite rewrite cong₂ aexp {(projΔ Δ wfe)} {(projΔ Δ wfe)} refl (eqDγ→τprojT₂ {an D x₂} {x₃} x)
                                            = projt₂ x₃ wfe e₁
   projt₂ {an S (α₁ • α₂)} (wf-pair wft wft₁ x x₁) wfe (APair .S x₂ e e₁) = projt₂ wft wfe e , projt₂ wft₁ wfe e₁
   projt₂ {an D (α₁ • α₂)} {Δ} (wf-pair wft wft₁ x x₁) wfe (APair .D x₂ e e₁) 
     = myrewrite1 ḋ myrewrite2
          where myrewrite1 : aexp (projΔ Δ wfe) (D (γ→τ (projT₂ α₁ wft)))
                myrewrite1 rewrite cong₂ aexp {(projΔ Δ wfe)} {(projΔ Δ wfe)} refl (eqDγ→τprojT₂ {α₁} {wft} x)
                     =  projt₂ wft wfe e
                myrewrite2 : aexp (projΔ Δ wfe) (D (γ→τ (projT₂ α₂ wft₁)))
                myrewrite2 rewrite cong₂ aexp {(projΔ Δ wfe)} {(projΔ Δ wfe)} refl (eqDγ→τprojT₂ {α₂} {wft₁} x₁)
                     =  projt₂ wft₁ wfe e₁
   projt₂ {an S (α₁ ⊎ α₂)} (wf-sum wft wft₁ x x₁) wfe (ATl .S x₂ e) = STl (projt₂ wft wfe e)
   projt₂ {an D (α₁ ⊎ α₂)} {Δ} (wf-sum wft wft₁ x x₁) wfe (ATl .D x₂ e) 
      = DTl myrewrite
           where myrewrite : aexp (projΔ Δ wfe) (D (γ→τ (projT₂ α₁ wft)))
                 myrewrite rewrite  cong₂ aexp {(projΔ Δ wfe)} {(projΔ Δ wfe)} refl (eqDγ→τprojT₂ {α₁} {wft} x)
                      = projt₂ wft wfe e
   projt₂ {an S (α₁ ⊎ α₂)} (wf-sum wft wft₁ x x₁) wfe (ATr .S x₂ e) = STr (projt₂ wft₁ wfe e)
   projt₂ {an D (α₁ ⊎ α₂)} {Δ} (wf-sum wft wft₁ x x₁) wfe (ATr .D x₂ e) 
      = DTr myrewrite
           where myrewrite : aexp (projΔ Δ wfe) (D (γ→τ (projT₂ α₂ wft₁)))
                 myrewrite rewrite cong₂ aexp {(projΔ Δ wfe)} {(projΔ Δ wfe)} refl (eqDγ→τprojT₂ {α₂} {wft₁} x₁)
                   = projt₂ wft₁ wfe e
   projt₂ {an x x₁} wft wfe (ACase {α₁} {α₂} {.(an x x₁)} {S} x₂ e e₁ e₂) with  αAExp→wft e 
   projt₂ {an x₂ x₃} wft wfe (ACase {α₁} {α₂} {.(an x₂ x₃)} {S} x₄ e e₁ e₂) | wf-sum WFT WFT₁ x x₁ 
      = SCase {γ₁ = projT₂ α₁ WFT} {γ₂ = projT₂ α₂ WFT₁}
          {γ₃ = projT₂ (an x₂ x₃) wft} (projt₂ (wf-sum WFT WFT₁ x x₁) wfe e) (projt₂ wft (wf-∷ WFT wfe) e₁) (projt₂ wft (wf-∷ WFT₁ wfe) e₂)
   projt₂ {an S x₁} wft wfe (ACase {α₁} {α₂} {.(an S x₁)} {D} () e e₁ e₂)
   projt₂ {an D x₁} wft wfe (ACase {α₁} {α₂} {.(an D x₁)} {D} x₂ e e₁ e₂) with αAExp→wft e 
   projt₂ {an D x₂} {Δ} wft wfe (ACase {α₁} {α₂} {.(an D x₂)} {D} x₃ e e₁ e₂) | wf-sum WFT WFT₁ x x₁
     = myrewrite
         where myrewrite :  aexp (projΔ Δ wfe) (projT₂ (an D x₂) wft)
               myrewrite  rewrite sym (cong₂ aexp {(projΔ Δ wfe)} {(projΔ Δ wfe)} refl (eqDγ→τprojT₂ {an D x₂} {wft} x₃))
                = DCase (projt₂ (wf-sum WFT WFT₁ x x₁) wfe e) myrewrite1 myrewrite2
                       where myrewrite1 : aexp (D (γ→τ (projT₂ α₁ WFT)) ∷ projΔ Δ wfe) (D (γ→τ (projT₂ (an D x₂) wft)))
                             myrewrite1 rewrite (cong₂ aexp (cong₂  (_∷_) {D (γ→τ (projT₂ α₁ WFT))} {projT₂ α₁ WFT} {projΔ Δ wfe} {projΔ Δ wfe} 
                                (eqDγ→τprojT₂ {α₁} {WFT} x) refl) (eqDγ→τprojT₂ {an D x₂} {wft} x₃))
                                  = projt₂ wft (wf-∷ WFT wfe) e₁
                             myrewrite2 : aexp (D (γ→τ (projT₂ α₂ WFT₁)) ∷ projΔ Δ wfe) (D (γ→τ (projT₂ (an D x₂) wft)))
                             myrewrite2 rewrite (cong₂ aexp (cong₂  (_∷_) {D (γ→τ (projT₂ α₂ WFT₁))} {projT₂ α₂ WFT₁} {projΔ Δ wfe} {projΔ Δ wfe} 
                                (eqDγ→τprojT₂ {α₂} {WFT₁} x₁) refl) (eqDγ→τprojT₂ {an D x₂} {wft} x₃))
                                  = projt₂ wft (wf-∷ WFT₁ wfe) e₂
          
   projt₂ {an D x₁} wft wfe (Lift x e) = {!!} 


   