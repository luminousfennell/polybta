module AnnotatedTypes where

{-

-- ATypes are stratified such that that dynamically bound
-- functions can only have dynamically bound parameters.

-- TODO: why exactly is that necessary?

-- Think about the example of the evaluation of a dynamic function with 
-- static components

-- The following well-formedness relation as an alternative representation
-- for this constraint:
module AType-WF where
  open import Relation.Binary.PropositionalEquality
  -- Static and dynamic binding times
  data BT : Set where
    stat : BT
    dyn : BT

  -- Ordering on binding times: dynamic binding time subsumes static
  -- binding time.
  data _≤-bt_ : BT → BT → Set where
    bt≤bt : ∀ bt → bt ≤-bt bt
    stat≤bt : ∀ bt → stat ≤-bt bt


  module WF (ATy : Set) (typeof : ATy → Type) (btof : ATy → BT) where
    data wf : ATy → Set where
      wf-int : ∀ α → typeof α ≡ Int → wf α
      wf-fun : ∀ α α₁ α₂ →
               typeof α ≡ Fun (typeof α₁) (typeof α₂) → 
               --btof α ≤-bt btof α₁ →
               --btof α ≤-bt btof α₂ →
               wf α₁ → wf α₂ →
               wf α
      -- Note that in [wf-fun],we can omit the checking of the label of
      -- the arguments against that of the function and [_≤-bt_] is 
      -- unnecessary
      wf-pair : ∀ α α₁ α₂ →
               typeof α ≡ typeof α₁ • typeof α₂ →
               wf α₁ → wf α₂ →
               wf α
      wf-sum  : ∀ α α₁ α₂ →
               typeof α ≡ typeof α₁ ⊎ typeof α₂ →
               wf α₁ → wf α₂ →
               wf α

  -- It is easy to check that the stratification respects the
  -- well-formedness, given the intended mapping from ATypes to
  -- binding times expained above:
  btof : AType → BT
  btof AInt = stat
  btof (AFun aty aty₁) = stat
  btof (D x) = dyn
  btof (aty • aty₁) = stat
  btof (aty ⊎ aty₁) = stat
  
  ---------------------
  -- Alternative [btof]
  ---------------------
  btof' : AType → BT
  btof' AInt = stat
  btof' (AFun aty aty₁) = stat
  btof' (D x) = dyn
  btof' (aty • aty₁) = dyn
  btof' (aty ⊎ aty₁) = dyn

  open WF AType typeof btof using (wf-fun; wf-int) renaming (wf to wf-AType)
  lem-wf-AType : ∀ α → wf-AType α
  lem-wf-AType AInt = WF.wf-int AInt refl
  lem-wf-AType (AFun α₁ α₂) = WF.wf-fun (AFun α₁ α₂) α₁ α₂ refl (lem-wf-AType α₁)
                                (lem-wf-AType α₂)
  lem-wf-AType (D Int) = WF.wf-int (D Int) refl
  lem-wf-AType (D (Fun x x₁)) = WF.wf-fun (D (Fun x x₁)) (D x) (D x₁) refl (lem-wf-AType (D x))
                                  (lem-wf-AType (D x₁))
  lem-wf-AType (D (x • x₁)) = WF.wf-pair (D (x • x₁)) (D x) (D x₁) refl (lem-wf-AType (D x))
                                (lem-wf-AType (D x₁))
  lem-wf-AType (D (x ⊎ x₁)) = WF.wf-sum (D (x ⊎ x₁)) (D x) (D x₁) refl (lem-wf-AType (D x))
                                (lem-wf-AType (D x₁))
  lem-wf-AType (α₁ • α₂) = WF.wf-pair (α₁ • α₂) α₁ α₂ refl (lem-wf-AType α₁) (lem-wf-AType α₂)
  lem-wf-AType (α₁ ⊎ α₂) = WF.wf-sum (α₁ ⊎ α₂) α₁ α₂ refl (lem-wf-AType α₁) (lem-wf-AType α₂)
  --lem-wf-AType AInt = WF.wf-int AInt refl
  --lem-wf-AType (AFun α α₁) = WF.wf-fun (AFun α α₁) α α₁ refl (stat≤bt (btof α))
  --                           (stat≤bt (btof α₁))
  --                          (lem-wf-AType α)
  --                           (lem-wf-AType α₁)
  --lem-wf-AType (D Int) = WF.wf-int (D Int) refl
  --lem-wf-AType (D (Fun x x₁)) = WF.wf-fun (D (Fun x x₁))
  --                                        (D x) (D x₁)
  --                                        refl (bt≤bt dyn) (bt≤bt dyn)
  --                                        (lem-wf-AType (D x))
  --                                        (lem-wf-AType (D x₁))

  -----------------------------------------
  -- Note that [lem-wf-AType] is based upon 
  -- a modified [wf]
  -----------------------------------------

-}