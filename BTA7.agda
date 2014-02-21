module BTA6 where

----------------------------------------------
-- Preliminaries: Imports and List-utilities
----------------------------------------------

open import Data.Nat hiding  (_<_;_⊔_;_*_;equal)
open import Data.Bool hiding (_∧_;_∨_) 
open import Function using (_∘_)
open import Data.List
open import Data.Nat.Properties
open import Relation.Nullary


-------------------------------
-- Some auxiliary constructions
-------------------------------
---------
-- Bottom
---------
--data ⊥ : Set where
--------------
-- Conjunction
--------------
data _∧_ (A : Set) (B : Set) : Set where
  ∧-intro : A → B → (A ∧ B)
--------------
-- Disjunction
--------------
--data _∨_ (A : Set) (B : Set) : Set where
--  ∨-introl : A → (A ∨ B)
--  ∨-intror : B → (A ∨ B)
--------------
-- Implication
--------------
--data _⇛_ (A : Set) (B : Set) : Set where
--  ⇛-intro : (f : A → B)  → A ⇛ B
-----------
-- Negation
-----------
--¬ : Set → Set
--¬ A = A ⇛ ⊥

--------------------------------
-- Extension with Pairs and Sums
--------------------------------

--------------------------------
-- Basic Set-up
--------------------------------
record Sg  (S : Set) (T : S → Set) : Set where
  constructor _,_
  field
    ffst : S
    ssnd : T ffst
open Sg public


--pair type on the agda level
_*_ : Set → Set → Set 
S * T = Sg S \ _ → T 
--proj functions on the agda level
fst : {A B : Set} → A * B → A
fst (a , b) =  a

snd : {A B : Set} → A * B → B
snd (a , b) =  b


--sum type on the agda level
data _⨄_ (A : Set) (B : Set) : Set where
  tl : (a : A) → A ⨄ B
  tr : (b : B) → A ⨄ B
------------------------------   
-- Some remark regarding [_⨄_]
------------------------------
-- a. Both constructors of [_⨄_] are injective
-- b. [tl] and [tr] are disjoint 


------------------------------------
-- End of Basic Set-up
------------------------------------

-- Pointer into a list. It is similar to list membership as defined in
-- Data.List.AnyMembership, rather than going through propositional
-- equality, it asserts the existence of the referenced element
-- directly.
module ListReference where 
  infix 4 _∈_
  data _∈_ {A : Set} : A → List A → Set where
    hd : ∀ {x xs} → x ∈ (x ∷ xs)
    tl : ∀ {x y xs} → x ∈ xs → x ∈ (y ∷ xs)
open ListReference

-- Extension of lists at the front and, as a generalization, extension
-- of lists somewhere in the middle.
module ListExtension where 
  open import Relation.Binary.PropositionalEquality

  -- Extension of a list by consing elements at the front. 
  data _↝_ {A : Set} : List A → List A → Set where
    ↝-refl   : ∀ {Γ}      → Γ ↝ Γ
    ↝-extend : ∀ {Γ Γ' τ} → Γ ↝ Γ' → Γ ↝ (τ ∷ Γ')
  
  -- Combining two transitive extensions. 
  ↝-trans : ∀ {A : Set}{Γ Γ' Γ'' : List A} → Γ ↝ Γ' → Γ' ↝ Γ'' → Γ ↝ Γ''
  ↝-trans Γ↝Γ' ↝-refl = Γ↝Γ'
  ↝-trans Γ↝Γ' (↝-extend Γ'↝Γ'') = ↝-extend (↝-trans Γ↝Γ' Γ'↝Γ'')
  
  -- Of course, ↝-refl is the identity for combining two extensions.
  lem-↝-refl-id : ∀ {A : Set} {Γ Γ' : List A} →
                    (Γ↝Γ' : Γ ↝ Γ') →
                    Γ↝Γ' ≡ (↝-trans ↝-refl Γ↝Γ')  
  lem-↝-refl-id ↝-refl = refl
  lem-↝-refl-id (↝-extend Γ↝Γ') = cong ↝-extend (lem-↝-refl-id Γ↝Γ')

  -- Extending a list in the middle: 
  data _↝_↝_ {A : Set} : List A → List A → List A → Set where
    -- First prepend the extension list to the common suffix
    ↝↝-base   : ∀ {Γ Γ''} → Γ ↝ Γ'' → Γ ↝ [] ↝ Γ'' 
    -- ... and then add the common prefix
    ↝↝-extend : ∀ {Γ Γ' Γ'' τ} →
                 Γ ↝ Γ' ↝ Γ'' → (τ ∷ Γ) ↝ (τ ∷ Γ') ↝ (τ ∷ Γ'') 
open ListExtension

---------------------------------------
-- Start of the development:
---------------------------------------

-- Intro/Objective:
-------------------
-- The following development defines a (verified) specializer/partial
-- evaluator for a simply typed lambda calculus embedded in Agda using
-- deBruijn indices.

-- The residual language.
-------------------------

-- The residual language is a standard simply typed λ-calculus.  The
-- types are integers,functions,pairs,and sums.
data Type : Set where
  Int : Type
  Fun : Type → Type → Type
    --pair type on the residual type level
  _•_ : Type  → Type  → Type   
  --sum type on the residual type level
  _⊎_ : Type → Type → Type

Ctx = List Type


-- The type Exp describes the typed residual expressions. Variables
-- are represented by deBruijn indices that form references into the
-- typing context. The constructors and typing constraints are
-- standard.

-- TODO: citations for ``as usual'' and ``standard''
-- what?
data Exp (Γ : Ctx) : Type → Set where
  EVar : ∀ {τ} → τ ∈ Γ → Exp Γ τ
  EInt : ℕ → Exp Γ Int
  EAdd : Exp Γ Int → Exp Γ Int -> Exp Γ Int
  ELam : ∀ {τ τ'} → Exp (τ ∷ Γ) τ' → Exp Γ (Fun τ τ')
  EApp : ∀ {τ τ'} → Exp Γ (Fun τ τ')  → Exp Γ τ → Exp Γ τ'
  _,_  : ∀ {τ τ'} → Exp Γ τ → Exp Γ τ' → Exp Γ (τ • τ')
  Tl   : ∀ {τ τ'} → Exp Γ τ → Exp Γ (τ ⊎ τ')
  Tr   : ∀ {τ τ'} → Exp Γ τ' → Exp Γ (τ ⊎ τ') 
  EFst : ∀ {τ τ'} → Exp Γ (τ • τ') → Exp Γ τ
  ESnd : ∀ {τ τ'} → Exp Γ (τ • τ') → Exp Γ τ'
  ECase : ∀ {τ τ' τ''} → Exp Γ (τ ⊎ τ') → Exp (τ ∷ Γ) τ'' → Exp (τ' ∷ Γ) τ'' → Exp Γ τ''


-- The standard functional semantics of the residual expressions. 
-- TODO: citations for ``as usual'' and ``standard''
-- what?
module Exp-Eval where
  -- interpretation of Exp types
  EImp : Type → Set
  EImp Int = ℕ
  EImp (Fun ty ty₁) = EImp ty → EImp ty₁
  EImp (ty • ty₁) = EImp ty * EImp ty₁
  EImp (ty ⊎ ty₁) = EImp ty ⨄ EImp ty₁



  -- Environments containing values for free variables. An environment
  -- is indexed by a typing context that provides the types for the
  -- contained values.
  data Env : Ctx → Set where 
    [] : Env []
    _∷_ : ∀ {τ Γ} → EImp τ → Env Γ → Env (τ ∷ Γ)
  
  -- Lookup a value in the environment, given a reference into the
  -- associated typing context.
  lookupE : ∀ { τ Γ } → τ ∈ Γ → Env Γ → EImp τ
  lookupE hd (x ∷ env) = x
  lookupE (tl v) (x ∷ env) = lookupE v env


  -- Evaluation of residual terms, given a suitably typed environment.
  ev : ∀ {τ Γ} → Exp Γ τ → Env Γ → EImp τ
  ev (EVar x) env = lookupE x env
  ev (EInt x) env = x
  ev (EAdd e e₁) env = ev e env + ev e₁ env
  ev (ELam e) env = λ x → ev e (x ∷ env)
  ev (EApp e e₁) env = ev e env (ev e₁ env)
  ev (e , e₁) env = ev e env , (ev e₁ env)
  ev (Tl e) env = tl (ev e env)
  ev (Tr e) env = tr (ev e env)
  ev (EFst e) env = fst (ev e env)
  ev (ESnd e) env = snd (ev e env)
  ev (ECase e e₁ e₂) env with ev e env
  ev (ECase e e₁ e₂) env | tl c  = (λ x → ev e₁ (x ∷ env)) c
  ev (ECase e e₁ e₂) env | tr c  = (λ x → ev e₂ (x ∷ env)) c


-- The binding-time-annotated language. 
---------------------------------------

-- The type of a term determines the term's binding time. The type
-- constructors with an A-prefix denote statically bound integers and
-- functions. Terms with dynamic binding time have a `D' type. The `D'
-- type constructor simply wraps up a residual type.
data AType : Set where
    AInt  : AType
    AFun  : AType → AType → AType
    D     : Type → AType
    --pair type on the annotated type level
    _•_   : AType → AType → AType 
    --sum  type on the annotated type level
    _⊎_   : AType → AType → AType 

ACtx = List AType



-- The mapping from annotated types to residual types is straightforward.
typeof : AType → Type
typeof AInt = Int
typeof (AFun α₁ α₂) = Fun (typeof α₁) (typeof α₂) 
typeof (D x) = x
typeof (α₁ • α₂) = typeof α₁ • typeof α₂
typeof (α₁ ⊎ α₂) = typeof α₁ ⊎ typeof α₂

ex-dpair : AType
ex-dpair = D (Int • Int)



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
           
-- The typed annotated terms: The binding times of variables is
-- determined by the corresponding type-binding in the context. In the
-- other cases, the A- and D-prefixes on term constructors inidicate
-- the corresponding binding times for the resulting terms.
data AExp (Δ : ACtx) : AType → Set where
  Var : ∀ {α} → α ∈ Δ → AExp Δ α
  AInt : ℕ → AExp Δ AInt
  AAdd : AExp Δ AInt → AExp Δ AInt → AExp Δ AInt
  ALam : ∀ {α₁ α₂}   → AExp (α₁ ∷ Δ) α₂ → AExp Δ (AFun α₁ α₂)
  AApp : ∀ {α₁ α₂}   → AExp Δ (AFun α₂ α₁) → AExp Δ α₂ → AExp Δ α₁
  DInt : ℕ → AExp Δ (D Int)
  DAdd : AExp Δ (D Int) → AExp Δ (D Int) → AExp Δ (D Int)
  DLam : ∀ {σ₁ σ₂}   → AExp ((D σ₁) ∷ Δ) (D σ₂) → AExp Δ (D (Fun σ₁ σ₂))
  DApp : ∀ {α₁ α₂}   → AExp Δ (D (Fun α₂ α₁)) → AExp Δ (D α₂) → AExp Δ (D α₁)
  -- Static pairs and sums
  _,_  : ∀ {α₁ α₂} → AExp Δ α₁ → AExp Δ α₂ → AExp Δ (α₁ • α₂)
  Tl   : ∀ {α₁ α₂} → AExp Δ α₁ → AExp Δ (α₁ ⊎ α₂)
  Tr   : ∀ {α₁ α₂} → AExp Δ α₂ → AExp Δ (α₁ ⊎ α₂)
  Fst  : ∀ {α₁ α₂} → AExp Δ (α₁ • α₂) → AExp Δ α₁
  Snd  : ∀ {α₁ α₂} → AExp Δ (α₁ • α₂) → AExp Δ α₂
  Case : ∀ {α₁ α₂ α₃} → AExp Δ (α₁ ⊎ α₂) → AExp (α₁ ∷ Δ) α₃ → AExp (α₂ ∷ Δ) α₃ → AExp Δ α₃
  -- Dynamic pairs and sums
  _ḋ_  : ∀ {σ₁ σ₂} → AExp Δ (D σ₁) → AExp Δ (D σ₂) → AExp Δ (D (σ₁ • σ₂))
  DTl   : ∀ {σ₁ σ₂} → AExp Δ (D σ₁) → AExp Δ (D (σ₁ ⊎ σ₂))
  DTr   : ∀ {σ₁ σ₂} → AExp Δ (D σ₂) → AExp Δ (D (σ₁ ⊎ σ₂))
  DFst  : ∀ {σ₁ σ₂} → AExp Δ (D (σ₁ • σ₂)) → AExp Δ (D σ₁)
  DSnd  : ∀ {σ₁ σ₂} → AExp Δ (D (σ₁ • σ₂)) → AExp Δ (D σ₂)
  DCase : ∀ {σ₁ σ₂ σ₃} → AExp Δ (D (σ₁ ⊎ σ₂)) → AExp ((D σ₁) ∷ Δ) (D σ₃) → AExp ((D σ₂) ∷ Δ) (D σ₃) → AExp Δ (D σ₃)

-- The terms of AExp assign a binding time to each subterm. For
-- program specialization, we interpret terms with dynamic binding
-- time as the programs subject to specialization, and their subterms
-- with static binding time as statically known inputs. A partial
-- evaluation function (or specializer) then compiles the program into
-- a residual term for that is specialized for the static inputs. The
-- main complication when defining partial evaluation as a total,
-- primitively recursive function will be the treatment of the De
-- Bruijn variables of non-closed residual expressions.

-- Before diving into the precise definition, it is instructive to
-- investigate the expected result of partial evaluation on some
-- examples.


module AExp-Examples where

  open import Data.Product
  
  -- (We pre-define some De Bruijn indices to improve
  -- readability of the examples:)
  x : ∀ {α Δ} → AExp (α ∷ Δ) α
  x = Var hd
  y : ∀ {α₁ α Δ} → AExp (α₁ ∷ α ∷ Δ) α
  y = Var (tl hd)
  z : ∀ {α₁ α₂ α Δ} → AExp (α₁ ∷ α₂ ∷ α ∷ Δ) α
  z = Var (tl (tl hd))

  -- A very simple case is the addition of three constants, where one
  -- is dynamically bound and two are bound statically:
  -- 5D +D (30S +S 7S)

  -- ex1 : AExp [] (D Int)
  -- ex1 = DAdd (DInt 5) (AAdd (AInt 30) (AInt 7))
  -- ex1' : AExp [] (D Int)
  -- ex1' = AApp (ALam (DAdd (DInt 5) x)) (AApp (ALam (DInt x) (AInt 30) (AInt 7)))

  -- TODO: this example does not work due to the very restrictive type
  -- off Add/DAdd. We could add a subsumption operator to AExp that
  -- turns a static expression into a dynamic one and then build a
  -- smart constructor for addition on top of that
  
  -- Note:This case is omitted in the same way as we impose the restriction that
  --      a dynamic function can only have components which are also dynamic.

  -- Another simple case is the specialization for a static identity
  -- function:
  -- (Sλ x → x) (42D)  ---specializes to--> 42D
  ex1 : AExp [] (D Int)
  ex1 = AApp (ALam (Var hd)) (DInt 42)

  ex1-spec : Exp [] Int
  ex1-spec = EInt 42

  -- The above example can be rewritten as an open AExp term that
  -- should be closed with a suitable environment. This representation
  -- does not only corresponds more directly with the notion of
  -- ``static inputs'', it also illustrates a typical situation when
  -- specializing the body of a lambda abstraction:

  -- The program ex1' takes an Int→Int function x as a static input.
  ex1' : AExp [ AFun (D Int) (D Int) ] (D Int)
  ex1' = AApp x (DInt 42)



  ---------------------
  -- Some more examples
  ---------------------
  ------------------
  -- Pairs
  ------------------
  ------------------
  -- a. Static Pairs
  ------------------
  ex2 : AExp [] (D Int)
  ex2 = Snd (AInt 42 , DInt 42)

  ex3 : AExp [] (D Int)
  ex3 = AApp (ALam (Snd (Var hd))) (AInt 42 , DInt 42)
  
  -- similar to ex1'
  ex3' : AExp [ AFun (AInt • (D Int)) (D Int) ] (D Int)
  ex3' = AApp x (AInt 42 , DInt 42)
  
  -------------------
  -- b. Dynamic Pairs
  -------------------
  ex4 : AExp [] (D Int)
  ex4 = AApp (ALam (DSnd (Var hd))) ( DInt 43 ḋ DInt 42)  

  -- similar to ex1'
  ex4' : AExp [ AFun (D (Int • Int)) (D Int) ] (D Int)
  ex4' = AApp x (DInt 43 ḋ DInt 42)


  ---------------------
  -- Sums
  ---------------------
  -----------------
  -- a. Static Sums
  -----------------
  ex5 : AExp [] AInt
  ex5 = Case {α₂ = AInt} (Tl (AInt 0))  (Var hd) (Var hd)

  ex6 : AExp [] AInt
  ex6 = Case {α₁ = AInt} (Tr (AInt 0))  (Var hd) (AInt 10)

  ex7 : AExp [] (AFun AInt AInt)
  ex7 = Case {α₂ = AInt} (Tl (ALam (Var hd))) (Var hd) (ALam (Var hd))

  ------------------
  -- b. Dynamic Sums
  ------------------
  ex8 : AExp [] (D Int)
  ex8 = DCase {σ₂ = Int} (DTl (DInt 0)) (Var hd) (Var hd)

  ex9 : AExp [] (D Int)
  ex9 = DCase {σ₁ = Int} (DTr (DInt 0)) (Var hd) (DInt 10)

  ex10 : AExp [] (D (Fun Int Int))
  ex10 = DCase {σ₂ = Int} (DTl (DLam (Var hd))) (Var hd) (DLam (Var hd))

 
  -- The partial evaluation of ex1' requires an environment to look up
  -- the static input. As a first approximation, a single input of
  -- type α is just some annotated term of type type α:
  Input : ∀ α → Set
  Input α = (∃ λ Δ → AExp Δ α)

  ----------------------------
  -- alternative specification
  ----------------------------
  --record Sg  (S : Set) (T : S → Set) : Set where
  --  constructor _,_
  --  field
  --    ffst : S
  --    ssnd : T ffst
  --open Sg public
  --Input' : ∀ α → Set
  --Input' α = Sg ACtx \ x → AExp x α 
  -- Note that [input'] should be equivalent to [input]

  -- (convenience constructor for Inputs)
  inp : ∀ {α Δ} → AExp Δ α → Input α
  inp {α} {Δ} e = Δ , e 
  -- An environment is simply a list of inputs that agrees with a
  -- given typing context.
  data AEnv : ACtx → Set where
    [] : AEnv []
    _∷_ : ∀ {α Δ} → Input α → AEnv Δ → AEnv (α ∷ Δ)

  lookup : ∀ {α Δ} → AEnv Δ → α ∈ Δ → Input α 
  lookup [] ()
  lookup (x ∷ env) hd = x
  lookup (x ∷ env) (tl id) = lookup env id

  -- Thus, an environment like ex1'-env should be able to close ex1'
  -- and a partial evaluation of the closure should yield the same
  -- result as in example ex1:
  ex1'-env : AEnv [ AFun (D Int) (D Int) ] 
  ex1'-env = inp (ALam {[]} {D Int} (Var hd)) ∷ []


  -- Similarly, an environment like ex3'-env should be able to close ex3'
  -- and a partial evaluation of the closure should yield the same
  -- result as in example ex3:
  ex3'-env : AEnv [ AFun (AInt • (D Int)) (D Int) ]
  ex3'-env = inp (ALam {[]} {AInt • (D Int)} (Snd (Var hd))) ∷ []

  
  -- Also, an environment like ex4'-env should be able to close ex4'
  -- and a partial evaluation of the closure should yield the same
  -- result as in example ex4:
  ex4'-env : AEnv [ AFun (D (Int • Int)) (D Int) ]
  ex4'-env = inp (ALam {[]} {D (Int • Int)} (DSnd (Var hd))) ∷ []  
  
  -- TODO: unit test
  ex1'-spec = ex1-spec
  ex3'-spec = ex1-spec
  ex4'-spec = ex1-spec
  

  -- (some definitions for the example)
  open import Data.Maybe
  _=<<_ : ∀ {A B : Set} → (A → Maybe B) → Maybe A → Maybe B
  f =<< mx = maybe′ f nothing mx
  liftM2 : ∀ {A B C : Set} → (A → B → Maybe C) → Maybe A → Maybe B → Maybe C
  liftM2 f mx my = (λ x → (λ y → f x y) =<< my) =<< mx


  -- The partial function ex1'-pe demonstrates the desired calculation
  -- for the specific case of ex1':
  ex1'-pe : ∀ {Δ} → AEnv Δ → AExp Δ (D Int) → Maybe (Exp [] Int)
  ex1'-pe {Δ} env (AApp ef ei)
    = liftM2 fromApp 
             (fromInput =<< fromVar ef)
             (fromInt ei)

    where fromInput : ∀ {α} → Input α → Maybe (Exp [] Int → Exp [] Int)
          fromInput (_ , ALam {D Int} (Var hd)) = just (λ x → x) 
          -- Sλ x/D → x
          fromInput _ = nothing
          fromVar : ∀ {α} → AExp Δ α → Maybe (Input α)
          fromVar (Var x) = just (lookup env x)
          fromVar _ = nothing
          fromApp : (Exp [] Int → Exp [] Int) → Exp [] Int → Maybe (Exp [] Int)
          fromApp f x = just (f x)
          fromInt : ∀ {α} → AExp Δ α → Maybe (Exp [] Int)
          fromInt (DInt i) = just (EInt {[]} i)
          fromInt _ = nothing
  ex1'-pe _ _ = nothing

  open import Relation.Binary.PropositionalEquality
  check-ex1'-pe : ex1'-pe ex1'-env ex1' ≡ just (ex1'-spec)
  check-ex1'-pe = refl


  -- Similarly the partial function ex3'-pe demonstrates the desired calculation
  -- for the specific case of ex3':

  ex3'-pe : ∀ {Δ} → AEnv Δ → AExp Δ (D Int) → Maybe (Exp [] Int)
  ex3'-pe {Δ} env (AApp ef ei)
    = liftM2 fromApp 
             (fromInput =<< fromVar ef)
             (fromPair ei)

    where fromInput : ∀ {α} → Input α → Maybe ((ℕ * (Exp [] Int)) → Exp [] Int)
          fromInput (_ , ALam {AInt • (D Int)} (Snd (Var hd))) = just (λ x → (snd x)) 
          -- Sλ x/(S*D) → (snd x)
          fromInput _ = nothing
          fromVar : ∀ {α} → AExp Δ α → Maybe (Input α)
          fromVar (Var x) = just (lookup env x)
          fromVar _ = nothing
          fromApp : ((ℕ  * (Exp [] Int)) → Exp [] Int) → (ℕ * (Exp [] Int)) → Maybe (Exp [] Int)
          fromApp f x = just (f x)
          fromPair : ∀ {α} → AExp Δ α → Maybe (ℕ * (Exp [] Int))
          fromPair ((AInt j) , (DInt i)) = just (j , (EInt {[]} i))
          fromPair _ = nothing
  ex3'-pe _ _ = nothing


  open import Relation.Binary.PropositionalEquality
  check-ex3'-pe : ex3'-pe ex3'-env ex3' ≡ just (ex3'-spec)
  check-ex3'-pe = refl


  -- Similarly the partial function ex3'-pe demonstrates the desired calculation
  -- for the specific case of ex3':

  ex4'-pe : ∀ {Δ} → AEnv Δ → AExp Δ (D Int) → Maybe (Exp [] Int)
  ex4'-pe {Δ} env (AApp ef ei)
    = liftM2 fromApp 
             (fromInput =<< fromVar ef)
             (fromDPair ei)

    where fromInput : ∀ {α} → Input α → Maybe (((Exp [] Int) * (Exp [] Int)) → Exp [] Int)
          fromInput (_ , ALam {D (Int • Int)} (DSnd (Var hd))) = just (λ x → (snd x)) 
          -- Sλ x/(S*D) → (snd x)
          fromInput _ = nothing
          fromVar : ∀ {α} → AExp Δ α → Maybe (Input α)
          fromVar (Var x) = just (lookup env x)
          fromVar _ = nothing
          fromApp : (((Exp [] Int)  * (Exp [] Int)) → Exp [] Int) → ((Exp [] Int) * (Exp [] Int)) → Maybe (Exp [] Int)
          fromApp f x = just (f x)
          fromDPair : ∀ {α} → AExp Δ α → Maybe ((Exp [] Int) * (Exp [] Int))
          fromDPair ((DInt j) ḋ (DInt i)) = just ((EInt {[]} j) , (EInt {[]} i))
          fromDPair _ = nothing
  ex4'-pe _ _ = nothing


  open import Relation.Binary.PropositionalEquality
  check-ex4'-pe : ex4'-pe ex4'-env ex4' ≡ just (ex4'-spec)
  check-ex4'-pe = refl

  -- The examples above show several problems for a total
  -- generalization to arbitrary term with the current datastructures:
  --  - the argument to fromApp is not primitive recursive
  
  -- What?
  
  --  - the result type of fromInput generates the context of the returned expression
  --    ``out of thin air''

  --  - Note "out of thin air" in a sense that the "typing context for the value" is only restricted by
  --    the value v itself thus any Δ which types v will do. Also note there is no connection between
  --    "typing context for the value" and the "typing context"

  -- TODO: continue


  -- Dλ y → let f = λ x → x D+ y in Dλ z → f z
  term1 : AExp [] (D (Fun Int (Fun Int Int)))
  term1 = DLam (AApp (ALam (DLam (AApp (ALam y) x)))
                     ((ALam (DAdd x y))))

-- Dλ y → let f = λ x → (Dλ w → x D+ y) in Dλ z → f z
-- Dλ y → (λ f → Dλ z → f z) (λ x → (Dλ w → x D+ y))
-- wrong
  term2 : AExp [] (D (Fun Int (Fun Int Int)))
  term2 = DLam (AApp (ALam (DLam (AApp (ALam y) x)))
                     ((ALam (DLam {σ₁ = Int} (DAdd y z)))))
-- ?
  term3 : AExp [] (D (Fun Int (Fun Int Int)))
  term3 = DLam (AApp (ALam (DLam (AApp (ALam y) x)))
                     (DInt 0))
  -- correct!
  term4 : AExp [] (D (Fun Int (Fun Int (Fun Int Int))))
  term4 = DLam (AApp (ALam (DLam (AApp y x)))
                     ((ALam (DLam {σ₁ = Int} (DAdd y z)))))
  ------------------
  -- Some more terms
  ------------------
  


-- The interpretation of annotated types. 
Imp : Ctx → AType → Set
Imp Γ (AInt) = ℕ
Imp Γ (AFun α₁ α₂) = ∀ {Γ'} → Γ ↝ Γ' → (Imp Γ' α₁ → Imp Γ' α₂)
Imp Γ (D σ) = Exp Γ σ
Imp Γ (α₁ • α₂) = (Imp Γ α₁) * (Imp Γ α₂)
Imp Γ (α₁ ⊎ α₂) = (Imp Γ α₁) ⨄ (Imp Γ α₂)



elevate-var : ∀ {Γ Γ'} {τ : Type} → Γ ↝ Γ' → τ ∈ Γ → τ ∈ Γ'
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
elevate Γ↝Γ'↝Γ'' (e ,  e₁) =  ((elevate Γ↝Γ'↝Γ'' e) , (elevate Γ↝Γ'↝Γ'' e₁))
elevate Γ↝Γ'↝Γ'' (Tl e) = Tl (elevate Γ↝Γ'↝Γ'' e)
elevate Γ↝Γ'↝Γ'' (Tr e) = Tr (elevate Γ↝Γ'↝Γ'' e)
elevate Γ↝Γ'↝Γ'' (EFst e) = EFst (elevate Γ↝Γ'↝Γ'' e)
elevate Γ↝Γ'↝Γ'' (ESnd e) = ESnd (elevate Γ↝Γ'↝Γ'' e)
elevate Γ↝Γ'↝Γ'' (ECase c e₁ e₂) = ECase (elevate Γ↝Γ'↝Γ'' c) (elevate (↝↝-extend Γ↝Γ'↝Γ'') e₁) (elevate (↝↝-extend Γ↝Γ'↝Γ'') e₂)



lift : ∀ {Γ Γ'} α → Γ ↝ Γ' → Imp Γ α → Imp Γ' α 
lift AInt p v = v
lift (AFun x x₁) Γ↝Γ' v = λ Γ'↝Γ'' → v (↝-trans Γ↝Γ' Γ'↝Γ'')
lift (D x₁) Γ↝Γ' v = elevate (↝↝-base Γ↝Γ') v
lift (α₁ • α₂) Γ↝Γ' (v₁ , v₂) = (lift α₁ Γ↝Γ' v₁) , (lift α₂ Γ↝Γ' v₂)
lift (α₁ ⊎ α₂) Γ↝Γ' (tl v) = tl (lift α₁ Γ↝Γ' v)
lift (α₁ ⊎ α₂) Γ↝Γ' (tr v) = tr (lift α₂ Γ↝Γ' v)





module SimpleAEnv where
  -- A little weaker, but much simpler
  data AEnv (Γ : Ctx) : ACtx → Set where
    [] : AEnv Γ []
    --cons : ∀ {Δ} (α : AType) → Imp Γ α → AEnv Γ Δ → AEnv Γ (α ∷ Δ)
    cons : ∀ {Δ} {α : AType} → Imp Γ α → AEnv Γ Δ → AEnv Γ (α ∷ Δ)
  
  lookup : ∀ {α Δ Γ} → AEnv Γ Δ → α ∈ Δ → Imp Γ α
  lookup [] ()
  --lookup {α} (cons .α  x aenv) hd = x
  --lookup {α} (cons .y  x aenv) (tl {.α} {y} id) = lookup aenv id
  lookup {α} (cons x aenv) hd = x
  lookup {α} (cons x aenv) (tl {.α} {y} id) = lookup aenv id
  
  liftEnv : ∀ {Γ Γ' Δ} → Γ ↝ Γ' → AEnv Γ Δ → AEnv Γ' Δ
  liftEnv Γ↝Γ' [] = []
  --liftEnv Γ↝Γ' (cons α x env) = cons α (lift α Γ↝Γ' x) (liftEnv Γ↝Γ' env)
  liftEnv Γ↝Γ' (cons {α = α} x env) = cons {α = α} (lift α Γ↝Γ' x) (liftEnv Γ↝Γ' env)
  
  consD : ∀ {Γ Δ} σ → AEnv Γ Δ → AEnv (σ ∷ Γ) (D σ ∷ Δ)
  --consD σ env = (cons (D σ) (EVar hd) (liftEnv (↝-extend {τ = σ} ↝-refl) env))
  consD σ env = (cons {α = D σ} (EVar hd) (liftEnv (↝-extend {τ = σ} ↝-refl) env))


  
  pe : ∀ {α Δ Γ} → AExp Δ α → AEnv Γ Δ → Imp Γ α
  pe (Var x) env = lookup env x
  pe (AInt x) env = x
  pe (AAdd e e₁) env = pe e env + pe e₁ env
  pe (ALam {α} e) env = λ Γ↝Γ' → λ y → pe e (cons {α = α} y (liftEnv Γ↝Γ' env))
  pe (AApp e e₁) env = pe e env ↝-refl (pe e₁ env)
  pe (DInt x) env = EInt x
  pe (DAdd e e₁) env = EAdd (pe e env) (pe e₁ env)
  pe (DLam {σ} e) env = ELam (pe e (consD σ env))
  pe (DApp e e₁) env = EApp (pe e env) (pe e₁ env)
  pe {Γ = Γ} (e , e₁) env = pe {Γ = Γ} e env , pe {Γ = Γ} e₁ env
  pe {α = α₁ ⊎ α₂} {Γ = Γ} (Tl e) env = tl (pe {α = α₁} {Γ = Γ} e env)
  pe {α = α₁ ⊎ α₂} {Γ = Γ} (Tr e) env = tr (pe {α = α₂} {Γ = Γ} e env)
  pe {Γ = Γ} (Fst e) env = fst (pe {Γ = Γ} e env)
  pe {Γ = Γ} (Snd e) env = snd (pe {Γ = Γ} e env)
  pe {Γ = Γ} (Case e e₁ e₂) env  with pe {Γ = Γ} e env
  pe {Γ = Γ} (Case {α₁ = α} e e₁ e₂) env | tl y = (λ Γ↝Γ' → λ y → pe e₁ (cons {α = α} y (liftEnv Γ↝Γ' env))) ↝-refl y
  pe {Γ = Γ} (Case {α₂ = α} e e₁ e₂) env | tr y = (λ Γ↝Γ' → λ y → pe e₂ (cons {α = α} y (liftEnv Γ↝Γ' env))) ↝-refl y
  pe (e ḋ e₁) env = pe e env , pe e₁ env
  pe (DTl e) env = Tl (pe e env)
  pe (DTr e) env = Tr (pe e env)
  pe (DFst e) env = EFst (pe e env)
  pe (DSnd e) env = ESnd (pe e env)
  pe (DCase {σ₁} {σ₂} e e₁ e₂) env = ECase (pe e env) (pe e₁ (consD σ₁ env)) (pe e₂ (consD σ₂ env))



module CheckExamples where
  open import Relation.Binary.PropositionalEquality
  open SimpleAEnv 
  open AExp-Examples 

  check-ex1 : pe ex1 [] ≡ ex1-spec
  check-ex1 = refl
  -------------
  -- Similarly
  ------------
  check-ex3 : pe ex3 [] ≡ ex1-spec
  check-ex3 = refl

  -------
  -- Also
  -------
  check-ex4 : pe {Γ = []} ex4 [] ≡ ESnd (EInt 43 , EInt 42)
  check-ex4 = refl


module Examples where
  open SimpleAEnv
  open import Relation.Binary.PropositionalEquality

  x : ∀ {α Δ} → AExp (α ∷ Δ) α
  x = Var hd
  y : ∀ {α₁ α Δ} → AExp (α₁ ∷ α ∷ Δ) α
  y = Var (tl hd)
  z : ∀ {α₁ α₂ α Δ} → AExp (α₁ ∷ α₂ ∷ α ∷ Δ) α
  z = Var (tl (tl hd))

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

  -------------------------- 
  -- Tests on pairs and sums
  --------------------------





-- Correctness proof

module Correctness where
  open SimpleAEnv
  open Exp-Eval

  -- TODO: rename occurences of stripα to typeof
  stripα = typeof

  stripΔ : ACtx → Ctx
  stripΔ = map stripα

  strip-lookup : ∀ { α Δ} → α ∈ Δ → stripα α ∈ stripΔ Δ
  strip-lookup hd = hd
  strip-lookup (tl x) = tl (strip-lookup x)



  strip : ∀ {α Δ} → AExp Δ α → Exp (stripΔ Δ) (stripα α)
  strip (Var x) = EVar (strip-lookup x)
  strip (AInt x) = EInt x
  strip (AAdd e e₁) = EAdd (strip e) (strip e₁)
  strip (ALam e) = ELam (strip e)
  strip (AApp e e₁) = EApp (strip e) (strip e₁)
  strip (DInt x) = EInt x
  strip (DAdd e e₁) = EAdd (strip e) (strip e₁)
  strip (DLam e) = ELam (strip e)
  strip (DApp e e₁) = EApp (strip e) (strip e₁)
  strip (e , e₁) = strip e , strip e₁
  strip (Tl e) = Tl (strip e)
  strip (Tr e) = Tr (strip e)
  strip (Fst e) = EFst (strip e)
  strip (Snd e) = ESnd (strip e)
  strip (Case e e₁ e₂) = ECase (strip e) (strip e₁) (strip e₂)
  strip (e ḋ e₁) = strip e , strip e₁
  strip (DTl e) = Tl (strip e)
  strip (DTr e) = Tr (strip e)
  strip (DFst e) = EFst (strip e)
  strip (DSnd e) = ESnd (strip e)
  strip (DCase e e₁ e₂) = ECase (strip e) (strip e₁) (strip e₂)




  liftE : ∀ {τ Γ Γ'} → Γ ↝ Γ' → Exp Γ τ → Exp Γ' τ
  liftE Γ↝Γ' e = elevate (↝↝-base Γ↝Γ') e

  stripLift : ∀ {α Δ Γ} → stripΔ Δ ↝ Γ → AExp Δ α  → Exp Γ (stripα α)
  stripLift Δ↝Γ = liftE Δ↝Γ ∘ strip

  -- We want to show that pe preserves the semantics of the
  -- program. Roughly, Exp-Eval.ev-ing a stripped program is
  -- equivalent to first pe-ing a program and then Exp-Eval.ev-ing the
  -- result. But as the pe-result of a static function ``can do more''
  -- than the (ev ∘ strip)ped function we need somthing more refined.

  module Equiv where
    open import Relation.Binary.PropositionalEquality

    -- Extending a value environment according to an extension of a
    -- type environment
    data _⊢_↝_ {Γ} : ∀ {Γ'} → Γ ↝ Γ' → Env Γ → Env Γ' → Set where
      refl : ∀ env → ↝-refl ⊢ env ↝ env
      extend : ∀ {τ Γ' env env'} →  {Γ↝Γ' : Γ ↝ Γ'} →
                 (v : EImp τ) → (Γ↝Γ' ⊢  env ↝ env')  →
                 ↝-extend Γ↝Γ' ⊢ env ↝ (v ∷ env')

    env↝trans : ∀ {Γ Γ' Γ''} {Γ↝Γ' : Γ ↝ Γ'} {Γ'↝Γ'' : Γ' ↝ Γ''}
                  {env env' env''} → 
                  Γ↝Γ' ⊢ env ↝ env' → Γ'↝Γ'' ⊢ env' ↝ env'' →
                  let Γ↝Γ'' = ↝-trans Γ↝Γ' Γ'↝Γ'' in
                  Γ↝Γ'' ⊢ env ↝ env'' 
    env↝trans {Γ} {.Γ''} {Γ''} {Γ↝Γ'} {.↝-refl} {env} {.env''} {env''} env↝env' (refl .env'') = env↝env'
    env↝trans env↝env' (extend v env'↝env'') = extend v (env↝trans env↝env' env'↝env'')
    

    -- Equivalent Imp Γ α and EImp τ values (where τ = stripα α). As
    -- (v : Imp Γ α) is not necessarily closed, equivalence is defined for
    -- the closure (Env Γ, ImpΓ α)
    Equiv : ∀ {α Γ} → Env Γ → Imp Γ α → EImp (stripα α) → Set
    Equiv {AInt} env av v = av ≡ v
    Equiv {AFun α₁ α₂} {Γ} env av v = ∀ {Γ' env' Γ↝Γ'} →
                                        (Γ↝Γ' ⊢ env ↝ env') →
                                        {av' : Imp Γ' α₁} →
                                        {v' : EImp (stripα α₁)} →
                                        Equiv env' av' v' → Equiv env' (av Γ↝Γ' av') (v v')
    Equiv {D x} env av v = ev av env ≡ v
    Equiv {α • α₁} env (ffst , ssnd) (ffst₁ , ssnd₁) = Equiv {α} env ffst ffst₁ ∧ Equiv {α₁} env ssnd ssnd₁
    Equiv {α ⊎ α₁} env (tl a) (tl a₁) = Equiv {α} env a a₁
    --------------------------------------------------------------------
    Equiv {α ⊎ α₁} env (tl a) (tr b) = false ≡ true  -- Interesting case!
    Equiv {α ⊎ α₁} env (tr b) (tl a) = false ≡ true  -- Interesting case!
    --------------------------------------------------------------------
    Equiv {α ⊎ α₁} env (tr b) (tr b₁) = Equiv {α₁} env b b₁ 
   -- Equiv {AInt} env av v = av ≡ v
   -- Equiv {AFun α₁ α₂} {Γ} env av v = -- extensional equality, given -- an extended context
   --     ∀ {Γ' env' Γ↝Γ'} → (Γ↝Γ' ⊢ env ↝ env') →
   --     {av' : Imp Γ' α₁} → {v' : EImp (stripα α₁)} →
   --     Equiv env' av' v' → Equiv env' (av Γ↝Γ' av') (v v')
   -- Equiv {D x} {Γ} env av v = ev av env ≡ v -- actually we mean extensional equality
                                             -- TODO: Define a proper equivalence for EImps
    
   

    -- Equivalence of AEnv and Env environments. They need to provide
    -- Equivalent bindings for a context Δ/stripΔ Δ. Again, the
    -- equivalence is defined for a closure (Env Γ', AEnv Γ' Δ).
    data Equiv-Env {Γ' : _} (env' : Env Γ') :
      ∀ {Δ} → let Γ = stripΔ Δ in
      AEnv Γ' Δ → Env Γ → Set where
      [] : Equiv-Env env' [] []
      cons : ∀ {α Δ} → let τ = stripα α
                           Γ = stripΔ Δ in
              {env : Env Γ} → {aenv : AEnv Γ' Δ} → 
              Equiv-Env env' aenv env →
              (va : Imp (Γ') α) → (v : EImp τ) → 
              Equiv env' va v → 
              --Equiv-Env env' (cons α va (aenv)) (v ∷ env)
              Equiv-Env env' (cons {α = α} va (aenv)) (v ∷ env)


  -- Now for the proof...
  module Proof where
    open Equiv
    open import Relation.Binary.PropositionalEquality

    -- Extensional equality as an axiom to prove the Equivalence of
    -- function values.  We could (should?) define it locally for
    -- Equiv.
    postulate ext : ∀ {τ₁ τ₂} {f g : EImp τ₁ → EImp τ₂} →
                    (∀ x → f x ≡ g x) → f ≡ g

    -- Ternary helper relation for environment extensions, analogous to _↝_↝_ for contexts
    data _⊢_↝_↝_⊣ : ∀ { Γ Γ' Γ''} → Γ ↝ Γ' ↝ Γ'' → Env Γ → Env Γ' → Env Γ'' → Set where
      refl : ∀ {Γ Γ''} {Γ↝Γ'' : Γ ↝ Γ''} { env env'' } →
             Γ↝Γ'' ⊢ env ↝ env'' →
             ↝↝-base Γ↝Γ'' ⊢ env ↝ [] ↝ env'' ⊣
      extend : ∀ {Γ Γ' Γ'' τ} {Γ↝Γ'↝Γ'' : Γ ↝ Γ' ↝ Γ''} { env env' env'' } →
               Γ↝Γ'↝Γ'' ⊢ env ↝ env' ↝ env'' ⊣ →
               (v : EImp τ) → ↝↝-extend Γ↝Γ'↝Γ'' ⊢ (v ∷ env) ↝ (v ∷ env') ↝ (v ∷ env'') ⊣



    -- the following lemmas are strong versions of the shifting
    -- functions, proving that consistent variable renaming preserves
    -- equivalence (and not just typing).
    lookup-elevate-≡ : ∀ {τ Γ Γ'} {Γ↝Γ' : Γ ↝ Γ'}
                       {env : Env Γ} {env' : Env Γ'} →
                       Γ↝Γ' ⊢ env ↝ env' → 
                       (x : τ ∈ Γ) → lookupE x env ≡ lookupE (elevate-var Γ↝Γ' x) env'
    lookup-elevate-≡ {τ} {.Γ'} {Γ'} {.↝-refl} {.env'} {env'} (refl .env') x = refl
    lookup-elevate-≡ (extend v env↝env') x = lookup-elevate-≡ env↝env' x

    lookup-elevate2-≡ : ∀ {τ Γ Γ' Γ''} {Γ↝Γ'↝Γ'' : Γ ↝ Γ' ↝ Γ''}
                       {env : Env Γ} {env' : Env Γ'} {env'' : Env Γ''} →
                       Γ↝Γ'↝Γ'' ⊢ env ↝ env' ↝ env'' ⊣ → 
                       (x : τ ∈ Γ) → lookupE x env ≡ lookupE (elevate-var2 Γ↝Γ'↝Γ'' x) env''
    lookup-elevate2-≡ (refl Γ↝Γ') x = lookup-elevate-≡ Γ↝Γ' x
    lookup-elevate2-≡ (extend env↝env'↝env'' v) hd = refl
    lookup-elevate2-≡ (extend env↝env'↝env'' _) (tl x)
      rewrite lookup-elevate2-≡ env↝env'↝env'' x = refl


    ---------------------------------
    -- helper functions for rewriting
    ---------------------------------
    →tl : ∀ {α α' x' y'} (x y : EImp (α ⊎ α'))→ x ≡ y →  x ≡ tl x' → y ≡ tl y' → x' ≡ y' 
    →tl {x' = x'} px py a b c rewrite b | c with py | a 
    ... | H | refl = refl
    -- →tl {α} {α'} {.y'} {y'} px py a b c | refl | ._ | refl | ._ | refl = ? -- rewrite b | c = {!!}
       
    →tr : ∀ {α α' x' y'} (x y : EImp (α ⊎ α'))→ x ≡ y →  x ≡ tr x' → y ≡ tr y' → x' ≡ y' 
    →tr px py a b c rewrite c | b with px | a 
    ... | H | refl = refl 
    ---------------------------------

    lem-elevate-≡ : ∀ {τ Γ Γ' Γ''}
                      {Γ↝Γ'↝Γ'' : Γ ↝ Γ' ↝ Γ''}
                      {env : Env Γ} {env' : Env Γ'} {env'' : Env Γ''} →
                      Γ↝Γ'↝Γ'' ⊢ env ↝ env' ↝ env'' ⊣ →
                      (e : Exp Γ τ) →
                      ev e env ≡ ev (elevate Γ↝Γ'↝Γ'' e) env''
    lem-elevate-≡ env↝env' (EVar x) = lookup-elevate2-≡ env↝env' x
    lem-elevate-≡ env↝env' (EInt x) = refl
    lem-elevate-≡ env↝env' (EAdd e e₁) with lem-elevate-≡ env↝env' e | lem-elevate-≡ env↝env' e₁
    ... | IA1 | IA2 = cong₂ _+_ IA1 IA2
    lem-elevate-≡ {Γ↝Γ'↝Γ'' = Γ↝Γ'↝Γ''}
                  {env = env}
                  {env'' = env''}
                  env↝env' (ELam e) = ext lem-elevate-≡-body
       where lem-elevate-≡-body : ∀ x → ev e (x ∷ env) ≡ ev (elevate (↝↝-extend Γ↝Γ'↝Γ'') e) (x ∷ env'')
             lem-elevate-≡-body x = lem-elevate-≡ (extend env↝env' x) e
    lem-elevate-≡ env↝env' (EApp e e₁) with lem-elevate-≡ env↝env' e | lem-elevate-≡ env↝env' e₁
    ... | IA1 | IA2  = cong₂ (λ f₁ x → f₁ x) IA1 IA2
    lem-elevate-≡ env↝env' (e , e₁) with lem-elevate-≡ env↝env' e | lem-elevate-≡ env↝env' e₁
    ... | IA1 | IA2  = cong₂ (λ x y → x , y) IA1 IA2
    lem-elevate-≡ env↝env' (Tl e) with lem-elevate-≡ env↝env' e
    ... | IA  = cong (λ x → tl x) IA
    lem-elevate-≡ env↝env' (Tr e) with lem-elevate-≡ env↝env' e
    ... | IA  = cong (λ x → tr x) IA
    lem-elevate-≡ env↝env' (EFst e) with lem-elevate-≡ env↝env' e 
    ... | IA  = cong (λ x → fst x) IA
    lem-elevate-≡ env↝env' (ESnd e) with lem-elevate-≡ env↝env' e
    ... | IA  = cong (λ x → snd x) IA
    lem-elevate-≡ {Γ↝Γ'↝Γ'' = Γ↝Γ'↝Γ''} 
                  {env = env}
                  {env'' = env''}
                  env↝env' (ECase e e₁ e₂) with ev e env | ev (elevate Γ↝Γ'↝Γ'' e) env'' | lem-elevate-≡ env↝env' e
    ... | tl c | tl c' | IA rewrite (→tl {x' = c} {y' = c'} (tl c) (tl c') IA refl refl) = lem-elevate-≡-body c'
         where lem-elevate-≡-body : ∀ x → ev e₁ (x ∷ env) ≡ ev (elevate (↝↝-extend Γ↝Γ'↝Γ'') e₁) (x ∷ env'')
               lem-elevate-≡-body x = lem-elevate-≡ (extend env↝env' x) e₁
    ... | tl c | tr c' | ()
    ... | tr c | tl c' | ()
    ... | tr c | tr c' | IA rewrite (→tr {x' = c} {y' = c'} (tr c) (tr c') IA refl refl) = lem-elevate-≡-body c'
         where lem-elevate-≡-body : ∀ x → ev e₂ (x ∷ env) ≡ ev (elevate (↝↝-extend Γ↝Γ'↝Γ'') e₂) (x ∷ env'')
               lem-elevate-≡-body x = lem-elevate-≡ (extend env↝env' x) e₂





    lem-lift-refl-id : ∀ {α Γ} → let τ = stripα α in
                       (env : Env Γ) →
                       (v : EImp τ) (va : Imp Γ α) →
                       Equiv env va v → 
                       Equiv env (lift α ↝-refl va) v
    lem-lift-refl-id {AInt} env v va eq = eq
    lem-lift-refl-id {AFun α α₁} {Γ} env v va eq = body
        where body : ∀ {Γ'} {env' : Env Γ'} {Γ↝Γ' : Γ ↝ Γ'} →
                     Γ↝Γ' ⊢ env ↝ env' →
                     {av' : Imp Γ' α} {v' : EImp (stripα α)} → 
                     Equiv env' av' v' → Equiv env' (va (↝-trans ↝-refl Γ↝Γ') av') (v v')
              body {Γ↝Γ' = Γ↝Γ'} env↝env' eq' rewrite sym (lem-↝-refl-id Γ↝Γ') = eq env↝env' eq' 
    
    lem-lift-refl-id {D x} env v va eq rewrite sym eq = sym (lem-elevate-≡ (refl (refl env)) va)
    lem-lift-refl-id {α • α₁} env (ffst , ssnd) (ffst₁ , ssnd₁) (∧-intro x x₁) = ∧-intro (lem-lift-refl-id {α} env ffst ffst₁ x) 
                                                                                         (lem-lift-refl-id {α₁} env ssnd ssnd₁ x₁)
    lem-lift-refl-id {α ⊎ α₁} env (tl a) (tl a₁) eq = lem-lift-refl-id  env a a₁ eq
    lem-lift-refl-id {α ⊎ α₁} env (tl a) (tr b) ()
    lem-lift-refl-id {α ⊎ α₁} env (tr b) (tl a) () 
    lem-lift-refl-id {α ⊎ α₁} env (tr b) (tr b₁) eq = lem-lift-refl-id  env b b₁ eq



  
    -- lifting an Imp does not affect equivalence
    lem-lift-equiv : ∀ {α Γ Γ'} → let τ = stripα α in
                     {Γ↝Γ' : Γ ↝ Γ'} →
                     (va : Imp Γ α) (v : EImp τ) →
                     {env : Env Γ} {env' : Env Γ'} → 
                     Γ↝Γ' ⊢ env ↝ env' → 
                     Equiv env va v →
                     Equiv env' (lift α Γ↝Γ' va) v
    lem-lift-equiv va v {.env'} {env'} (refl .env') eq = lem-lift-refl-id env' v va eq 
    lem-lift-equiv {AInt} va v (extend v₁ env↝env') eq = eq
    lem-lift-equiv {AFun α α₁} va v (extend v₁ env↝env') eq = 
      λ v₁env₁↝env' eq₁ → eq (env↝trans (extend v₁ env↝env') v₁env₁↝env') eq₁
    lem-lift-equiv {D x} va v (extend v₁ env↝env') eq rewrite sym eq = sym (lem-elevate-≡ (refl (extend v₁ env↝env')) va)
    lem-lift-equiv {α • α₁} (ffst , ssnd) (ffst₁ , ssnd₁) (extend v₁ env↝env') (∧-intro x x₁) =
      ∧-intro (lem-lift-equiv {α} ffst ffst₁ (extend v₁ env↝env') x) (lem-lift-equiv {α₁} ssnd ssnd₁ (extend v₁ env↝env') x₁)
    lem-lift-equiv {α ⊎ α₁} (tl a) (tl a₁) (extend v₁ env↝env') eq = lem-lift-equiv  a a₁ (extend v₁ env↝env') eq
    lem-lift-equiv {α ⊎ α₁} (tl a) (tr b) (extend v₁ env↝env') () 
    lem-lift-equiv {α ⊎ α₁} (tr b) (tl a) (extend v₁ env↝env') ()
    lem-lift-equiv {α ⊎ α₁} (tr b) (tr b₁) (extend v₁ env↝env') eq = lem-lift-equiv  b b₁ (extend v₁ env↝env') eq




    lem-equiv-lookup : ∀ {α Δ Γ'} → let Γ = stripΔ Δ in
                       { aenv : AEnv Γ' Δ } {env : Env Γ} →
                       (env' : Env Γ') →
                       Equiv-Env env' aenv env →
                       ∀ x → Equiv {α} env' (lookup aenv x) (lookupE (strip-lookup x) env)
    lem-equiv-lookup env' [] ()
    lem-equiv-lookup env' (cons  enveq va v eq) hd = eq
    lem-equiv-lookup env' (cons  enveq va v eq) (tl x) = lem-equiv-lookup env' enveq x

    lem-equiv-env-lift-extend :
      ∀ {σ Γ' Δ} (env' : Env Γ') → let Γ = stripΔ Δ in
        {env : Env Γ} {aenv : AEnv Γ' Δ} →
        Equiv-Env env' aenv env → (x : EImp σ) →
        Equiv-Env (x ∷ env') (liftEnv (↝-extend ↝-refl) aenv) env
    lem-equiv-env-lift-extend _ [] x = []
    lem-equiv-env-lift-extend env' (cons {α} eqenv va v x) x₁ =
      cons (lem-equiv-env-lift-extend env' eqenv x₁)
           (lift α (↝-extend ↝-refl) va) v (lem-lift-equiv va v (extend x₁ (refl env')) x)

    lem-equiv-env-lift-lift :
      ∀ {Γ' Γ'' Δ} → let Γ = stripΔ Δ in
        {Γ↝Γ' : Γ' ↝ Γ''}
        {env' : Env Γ'} {env'' : Env Γ''}
        (env'↝env'' : Γ↝Γ' ⊢ env' ↝ env'') →
        {env : Env Γ} {aenv : AEnv Γ' Δ} →
        Equiv-Env env' aenv env → 
        Equiv-Env env'' (liftEnv Γ↝Γ' aenv) env
    lem-equiv-env-lift-lift env'↝env'' [] = []
    lem-equiv-env-lift-lift {Γ↝Γ' = Γ↝Γ'} env'↝env'' (cons {α} eqenv va v x)
      with lem-equiv-env-lift-lift env'↝env'' eqenv
    ... | IA = cons IA (lift α Γ↝Γ' va) v (lem-lift-equiv va v env'↝env'' x)



    -- When we partially evaluate somthing under an environment , it
    -- will give equivalent results to a ``complete'' evaluation under
    -- an equivalent environment 
    pe-correct : ∀ { α Δ Γ' } → (e : AExp Δ α) →
                 let Γ = stripΔ Δ in 
                 {aenv : AEnv Γ' Δ} → {env : Env Γ} → 
                 (env' : Env Γ') →
                 Equiv-Env env' aenv env → 
                 Equiv env' (pe e aenv) (ev (strip e) env)
    pe-correct (Var x) env' eqenv = lem-equiv-lookup env' eqenv x
    pe-correct (AInt x) env' eqenv = refl
    pe-correct (AAdd e e₁) env' eqenv 
      rewrite pe-correct e env' eqenv | pe-correct e₁ env' eqenv = refl
    pe-correct (ALam e) env' eqenv = 
     λ {_} {env''} env'↝env'' {av'} {v'} eq →
         let eqenv' : _
             eqenv' = lem-equiv-env-lift-lift env'↝env'' eqenv
             eqenv'' : _
             eqenv'' = cons eqenv' av' v' eq
         in pe-correct e env'' eqenv''
    pe-correct (AApp e e₁) env' eqenv 
      with pe-correct e env' eqenv | pe-correct e₁ env' eqenv
    ... | IAe | IAf = IAe (refl env') IAf
    pe-correct (DInt x) env' eqenv = refl
    pe-correct (DAdd e e₁) env' eqenv
      rewrite pe-correct e env' eqenv | pe-correct e₁ env' eqenv = refl
    pe-correct (DLam e) env' eqenv = 
     ext
      (λ x →
         let eqenv₁ : _
             eqenv₁ = lem-equiv-env-lift-extend env' eqenv x
             eqenv₂ : _
             eqenv₂ = cons eqenv₁ (EVar hd) x refl
         in pe-correct e (x ∷ env') eqenv₂)
    pe-correct (DApp e e₁) env' eqenv 
      with pe-correct e₁ env' eqenv | pe-correct e env' eqenv
    ... | IA' | IA = cong₂ (λ f x → f x) IA IA'
    pe-correct (e , e₁) env' eqenv = ∧-intro (pe-correct e env' eqenv) (pe-correct e₁ env' eqenv)
    pe-correct (Tl e) env' eqenv = pe-correct e env' eqenv
    pe-correct (Tr e) env' eqenv = pe-correct e env' eqenv
    pe-correct (Fst (e , e₁)) env' eqenv = pe-correct e env' eqenv
    pe-correct (Fst e) {aenv = aenv} {env = env} env' eqenv with pe e aenv | ev (strip e) env | pe-correct e env' eqenv
    ... | e₁ , e₂ | e₁' , e₂' | ∧-intro A B = A
    pe-correct (Snd (e , e₁)) env' eqenv = pe-correct e₁ env' eqenv
    pe-correct (Snd e) {aenv = aenv} {env = env} env' eqenv with pe e aenv | ev (strip e) env | pe-correct e env' eqenv
    ... | e₁ , e₂ | e₁' , e₂' | ∧-intro A B = B
    pe-correct {α} (Case e e₁ e₂) {aenv = aenv} {env = env} env' eqenv with pe e aenv | ev (strip e) env | pe-correct e env' eqenv
    ... | tl c | tl c' | L = pe-correct e₁ {aenv = cons c (liftEnv ↝-refl aenv)}
                               {env = c' ∷ env} env'
                               (cons (lem-equiv-env-lift-lift (refl env') eqenv) c c' L)
    ... | tr c | tr c' | R = pe-correct e₂ {aenv = cons c (liftEnv ↝-refl aenv)}
                               {env = c' ∷ env} env'
                               (cons (lem-equiv-env-lift-lift (refl env') eqenv) c c' R)
    ... | tr c | tl c' | ()
    ... | tl c | tr c' | ()
    pe-correct (e ḋ e₁) env' eqenv with pe-correct e env' eqenv | pe-correct e₁ env' eqenv 
    ... | IA | IA' rewrite IA | IA' = refl
    pe-correct (DTl e) env' eqenv with pe-correct e env' eqenv
    ... | IA rewrite IA = refl
    pe-correct (DTr e) env' eqenv with pe-correct e env' eqenv 
    ... | IA rewrite IA = refl
    pe-correct (DFst e) env' eqenv with pe-correct e env' eqenv 
    ... | IA rewrite IA = refl
    pe-correct (DSnd e) env' eqenv with pe-correct e env' eqenv
    ... | IA rewrite IA = refl
    pe-correct (DCase e e₁ e₂) {aenv = aenv} {env = env} env' eqenv with ev (pe e aenv) env' | ev (strip e) env | pe-correct e env' eqenv
    ... | tl c | tl c' | IA rewrite (→tl {x' = c} {y' = c'} (tl c) (tl c') IA refl refl) = 
      pe-correct e₁
        {aenv = cons (EVar hd) (liftEnv (↝-extend ↝-refl) aenv)}
        {env = c' ∷ env} (c' ∷ env') (cons (lem-equiv-env-lift-lift (extend c' (refl env')) eqenv) (EVar hd) c' refl)
    ... | tr c | tr c' | IA rewrite (→tr {x' = c} {y' = c'} (tr c) (tr c') IA refl refl) = 
      pe-correct e₂
        {aenv = cons (EVar hd) (liftEnv (↝-extend ↝-refl) aenv)}
        {env = c' ∷ env} (c' ∷ env')
        (cons (lem-equiv-env-lift-lift (extend c' (refl env')) eqenv)
         (EVar hd) c' refl)
    ... | tl c | tr c' | ()  
    ... | tr c | tl c' | ()



    
    --pe-correct (Var x) env' eqenv = lem-equiv-lookup env' eqenv x
    --pe-correct (AInt x) env' eqenv = refl
    --pe-correct (AAdd e f) env' eqenv
    --  rewrite pe-correct e env' eqenv | pe-correct f env' eqenv = refl
    --pe-correct (ALam e) env' eqenv =
    --  λ {_} {env''} env'↝env'' {av'} {v'} eq →
    --    let eqenv' = (lem-equiv-env-lift-lift env'↝env'' eqenv)
    --        eqenv'' = (cons eqenv' av' v' eq)
    --    in pe-correct e env'' eqenv''
    --pe-correct (AApp e f) env' eqenv
    --  with pe-correct e env' eqenv | pe-correct f env' eqenv
    --... | IAe | IAf = IAe (refl env') IAf
    --pe-correct (DInt x) env' eqenv = refl
    --pe-correct (DAdd e f) env' eqenv 
    --  rewrite pe-correct e env' eqenv | pe-correct f env' eqenv = refl
    --pe-correct (DLam e) env' eqenv =
    --  ext (λ x → let eqenv' = (lem-equiv-env-lift-extend env' eqenv x)
    --                 eqenv'' = (cons eqenv' (EVar hd) x refl)
    --             in pe-correct e (x ∷ env') eqenv'')
    --pe-correct (DApp e f) {env = env} env' eqenv
    --  with pe-correct f env' eqenv | pe-correct e env' eqenv 
    --... | IA' | IA = cong₂ (λ f x → f x) IA IA'



-- module PreciseAEnv where
--   open Exp-Eval
--   open import Relation.Binary.PropositionalEquality

--   data AEnv : Ctx → ACtx → Set where
--     [] : AEnv [] []
--     cons : ∀ { Γ Γ' Δ } (α : AType) → Γ ↝ Γ' → Imp Γ' α → AEnv Γ Δ → AEnv Γ' (α ∷ Δ)

--   consD : ∀ {Γ Δ} σ → AEnv Γ Δ → AEnv (σ ∷ Γ) (D σ ∷ Δ)
--   consD σ env = (cons (D σ) (↝-extend {τ = σ} ↝-refl) (EVar hd) (env))

--   lookup : ∀ {α Δ Γ} → AEnv Γ Δ → α ∈ Δ → Imp Γ α
--   lookup (cons α _ v env) hd =  v 
--   lookup (cons α₁ Γ↝Γ' v env) (tl x) = lookup (cons α₁ Γ↝Γ' v env) (tl x) 
  
--   pe : ∀ {α Δ Γ} → AExp Δ α → AEnv Γ Δ → Imp Γ α
--   pe (Var x) env = lookup env x 
--   pe (AInt x) env = x
--   pe (AAdd e₁ e₂) env = pe e₁ env + pe e₂ env
--   pe (ALam {α} e) env = λ Γ↝Γ' → λ y → pe e (cons α Γ↝Γ' y env) 
--   pe (AApp e₁ e₂) env = ((pe e₁ env) ↝-refl) (pe e₂ env)
--   pe (DInt x) env = EInt x
--   pe (DAdd e e₁) env = EAdd (pe e env) (pe e₁ env)
--   pe (DLam {σ} e) env = ELam (pe e (consD σ env))
--   pe (DApp e e₁) env = EApp (pe e env) (pe e₁ env)

--   -- What is a suitable environment to interpret an AExp without pe? 
--   -- 1-1 mapping from AExp into Exp
--   stripα : AType → Type
--   stripα AInt = Int
--   stripα (AFun α₁ α₂) = Fun (stripα α₁) (stripα α₂)
--   stripα (D x) = x

--   stripΔ : ACtx → Ctx
--   stripΔ = map stripα

--   stripEnv : ∀ {Δ} →
--              let Γ = stripΔ Δ
--              in AEnv Γ Δ → Env Γ
--   stripEnv [] = []
--   stripEnv (cons AInt Γ↝Γ' v env) = v ∷ (stripEnv {!!})
--   stripEnv (cons (AFun α α₁) Γ↝Γ' v env) = {!!}
--   stripEnv (cons (D x) Γ↝Γ' v env) = {!!}

--   -- Extending a value environment according to an extension of a type environment 
--   data _⊢_↝_ {Γ} : ∀ {Γ'} → Γ ↝ Γ' → Env Γ → Env Γ' → Set where
--     refl : ∀ env → ↝-refl ⊢ env ↝ env
--     extend : ∀ {τ Γ' env env'} →  {Γ↝Γ' : Γ ↝ Γ'} →
--                (v : EImp τ) → (Γ↝Γ' ⊢  env ↝ env')  →
--                ↝-extend Γ↝Γ' ⊢ env ↝ (v ∷ env')
  
--   -- It turns out that we have to shift Exp also
--   liftE : ∀ {τ Γ Γ'} → Γ ↝ Γ' → Exp Γ τ → Exp Γ' τ
--   liftE Γ↝Γ' e = elevate (↝↝-base Γ↝Γ') e
  
--   Equiv : ∀ {α Γ} → Env Γ → Imp Γ α → EImp (stripα α) → Set 
--   Equiv {AInt} env av v = av ≡ v
--   Equiv {AFun α₁ α₂} {Γ} env av v = -- an pe-d static function is
--                                     -- equivalent to an EImp value
--                                     -- if given an suitably extended
--                                     -- environment, evaluating the
--                                     -- body yields something
--                                       -- equivalent to the EImp-value
--     ∀ {Γ' env' Γ↝Γ'} → (Γ↝Γ' ⊢ env ↝ env') →
--       {av' : Imp Γ' α₁} → {v' : EImp (stripα α₁)} →
--       Equiv env' av' v' → Equiv env' (av Γ↝Γ' av') (v v')
--   Equiv {D x} {Γ} env av v = ev av env ≡ v 

--   data Equiv-Env : ∀ {Δ} → let Γ = stripΔ Δ in
--                    AEnv Γ Δ → Env Γ → Set where
--     [] : Equiv-Env [] []
--     -- cons : ∀ {α Δ} → let Γ = stripΔ Δ in 
           
--     --         (va : Imp Γ α) → (v : EImp (stripα α)) →
--     --         (env : Env Γ) → Equiv env v va →
--     --         (aenv : AEnv Γ Δ) →
--     --         Equiv-Env aenv env →
--     --         Equiv-Env {α ∷ Δ} (cons α (lift α (↝-extend ↝-refl) va)
--     --                                   (liftEnv (↝-extend ↝-refl) aenv))
--     --                           (v ∷ env)
