module BTA6 where

----------------------------------------------
-- Preliminaries: Imports and List-utilities
----------------------------------------------

open import Data.Nat hiding (_<_)
open import Data.Bool
open import Function using (_∘_)
open import Data.List
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Category.Functor

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

mapIdx : {A B : Set} → (f : A → B) →
         {x : A} {xs : List A} → x ∈ xs → f x ∈ map f xs
mapIdx f hd = hd
mapIdx f (tl x₁) = tl (mapIdx f x₁)

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
  lem-↝-refl-id (↝-extend Γ↝Γ') =
    cong ↝-extend (lem-↝-refl-id Γ↝Γ')
  -- TODO: why does this work?
  -- lem-↝-refl-id (↝-extend Γ↝Γ') = lem-↝-refl-id (↝-extend Γ↝Γ')

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
-- types are integers and functions.
data Type : Set where
  Int : Type
  Fun : Type → Type → Type
Ctx = List Type

-- The type Exp describes the typed residual expressions. Variables
-- are represented by deBruijn indices that form references into the
-- typing context. The constructors and typing constraints are
-- standard.

-- TODO: citations for ``as usual'' and ``standard''
data Exp (Γ : Ctx) : Type → Set where
  EVar : ∀ {τ} → τ ∈ Γ → Exp Γ τ
  EInt : ℕ → Exp Γ Int
  EAdd : Exp Γ Int → Exp Γ Int -> Exp Γ Int
  ELam : ∀ {τ τ'} → Exp (τ ∷ Γ) τ' → Exp Γ (Fun τ τ')
  EApp : ∀ {τ τ'} → Exp Γ (Fun τ τ')  → Exp Γ τ → Exp Γ τ'

-- The standard functional semantics of the residual expressions. 
-- TODO: citations for ``as usual'' and ``standard''
module Exp-Eval where
  -- interpretation of Exp types
  EImp : Type → Set
  EImp Int = ℕ
  EImp (Fun τ₁ τ₂) = EImp τ₁ → EImp τ₂

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
  ev (EAdd e f) env = ev e env + ev f env
  ev (ELam e) env = λ x → ev e (x ∷ env)
  ev (EApp e f) env = ev e env (ev f env)


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
ACtx = List AType

-- The mapping from annotated types to residual types is straightforward.
typeof : AType → Type
typeof AInt = Int
typeof (AFun α₁ α₂) = Fun (typeof α₁) (typeof α₂)
typeof (D x) = x

-- ATypes are stratified such that that dynamically bound
-- functions can only have dynamically bound parameters.

-- TODO: why exactly is that necessary?

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
               btof α ≤-bt btof α₁ →
               btof α ≤-bt btof α₂ →
               wf α₁ → wf α₂ →
               wf α

  -- It is easy to check that the stratification respects the
  -- well-formedness, given the intended mapping from ATypes to
  -- binding times expained above:
  btof : AType → BT
  btof AInt = stat
  btof (AFun _ _) = stat
  btof (D x) = dyn

  open WF AType typeof btof using (wf-fun; wf-int) renaming (wf to wf-AType)
  lem-wf-AType : ∀ α → wf-AType α
  lem-wf-AType AInt = WF.wf-int AInt refl
  lem-wf-AType (AFun α α₁) = WF.wf-fun (AFun α α₁) α α₁ refl (stat≤bt (btof α))
                             (stat≤bt (btof α₁))
                             (lem-wf-AType α)
                             (lem-wf-AType α₁)
  lem-wf-AType (D Int) = WF.wf-int (D Int) refl
  lem-wf-AType (D (Fun x x₁)) = WF.wf-fun (D (Fun x x₁))
                                          (D x) (D x₁)
                                          refl (bt≤bt dyn) (bt≤bt dyn)
                                          (lem-wf-AType (D x))
                                          (lem-wf-AType (D x₁))
             
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
  DLam : ∀ {σ₁ σ₂} → AExp ((D σ₁) ∷ Δ) (D σ₂) → AExp Δ (D (Fun σ₁ σ₂))
  DApp : ∀ {α₁ α₂} → AExp Δ (D (Fun α₂ α₁)) → AExp Δ (D α₂) → AExp Δ (D α₁)
  Lift : AExp Δ AInt → AExp Δ (D Int)

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

module ApplicativeMaybe where
  open import Data.Maybe public
  open import Category.Functor public
  import Level
  open RawFunctor {Level.zero} functor public

  infixl 4 _⊛_
  _⊛_ : {A B : Set} → Maybe (A → B) → Maybe A → Maybe B
  just f ⊛ just x = just (f x)
  _ ⊛ _           = nothing


  liftA2 : {A B C : Set} → (A → B → C) → Maybe A → Maybe B → Maybe C 
  liftA2 f mx my = just f ⊛ mx ⊛ my

module AExp-Examples where

  open import Data.Product hiding (map)
  open ApplicativeMaybe
  open import Data.Empty
  open Relation.Binary.PropositionalEquality
  
  -- (We pre-define some De Bruijn indices to improve
  -- readability of the examples:)
  x : ∀ {α Δ} → AExp (α ∷ Δ) α
  x = Var hd
  x' : ∀ {α Δ} → Exp (α ∷ Δ) α
  x' = EVar hd
  y : ∀ {α₁ α Δ} → AExp (α₁ ∷ α ∷ Δ) α
  y = Var (tl hd)
  z : ∀ {α₁ α₂ α Δ} → AExp (α₁ ∷ α₂ ∷ α ∷ Δ) α
  z = Var (tl (tl hd))

  -- A rather trivial case is the specialization of base-type
  -- calulations. Here, we simply want to emit the result of a static
  -- addition as a constant:

  -- Lift (5S +S 5S) --specializes to --> 5E
  ex0 : AExp [] (D Int)
  ex0 = (Lift (AAdd (AInt 5) (AInt 5)))

  ex0' : AExp [] (D Int)
  ex0' = DAdd (DInt 6) (Lift (AAdd (AInt 5) (AInt 5)))

  ex0-spec : Exp [] Int
  ex0-spec = (EInt 10)

  ex0'-spec : Exp [] Int
  ex0'-spec = (EAdd (EInt 6) (EInt 10))

  -- The partial evaluation for this case is of course
  -- straightforward. We use Agda's ℕ as an implementation type for
  -- static integers and residual expressions Exp for dynamic ones.
  Imp0 : AType → Set
  Imp0 AInt = ℕ
  Imp0 (D σ) = Exp [] σ
  Imp0 _ = ⊥ 

  pe-ex0 : ∀ { α } → AExp [] α → Maybe (Imp0 α)
  pe-ex0 (AInt x) = just (x)
  pe-ex0 (DInt x) = just (EInt x)
  pe-ex0 (AAdd e f) = liftA2 _+_  (pe-ex0 e) (pe-ex0 f) 
  pe-ex0 (DAdd e f) = liftA2 EAdd (pe-ex0 e) (pe-ex0 f) 
  pe-ex0 (Lift e) = EInt <$> (pe-ex0 e)
  pe-ex0 _ = nothing

  ex0-test : pe-ex0 ex0 ≡ just ex0-spec
  ex0-test = refl

  ex0'-test : pe-ex0 ex0' ≡ just ex0'-spec
  ex0'-test = refl

  -- Specializing open terms is also straightforward. This situation
  -- typically arises when specializing the body of a lambda
  -- abstraction.
  -- (Dλ x → x +D Lift (5S + 5S)) ---specializes to--> Eλ x → EInt 10
  ex1 : AExp [] (D (Fun Int Int))
  ex1 = (DLam (DAdd x (Lift (AAdd (AInt 5) (AInt 5)))))

  ex1-spec : Exp [] (Fun Int Int)
  ex1-spec = ELam (EAdd x' (EInt 10))

  ex1' : AExp (D Int ∷ []) (D Int) 
  ex1' = (Lift (AAdd (AInt 5) (AInt 5)))

  ex1'-spec : Exp (Int ∷ []) Int 
  ex1'-spec = (EAdd x' (EInt 10))

  -- The implementation type now also has to hold open residual terms,
  -- which arise as the result of partially evaluating an open term
  -- with with dynamic binding time. The calculation of the
  -- implementation type thus requires a typing context as a
  -- parameter.
  Imp1 : Ctx → AType → Set
  Imp1 _ AInt = ℕ
  Imp1 Γ (D τ) = Exp Γ τ
  Imp1 _ _ = ⊥

  erase = typeof

  -- Unsurprisingly, Partial evaluation of open terms emits
  -- implementations that are typed under the erased context.
  pe-ex1 : ∀ {α Δ} → AExp Δ α → Maybe (Imp1 (map erase Δ) α)
  pe-ex1 (AInt x) = just (x)
  pe-ex1 (DInt x) = just (EInt x)
  pe-ex1 (AAdd e f) = liftA2 _+_  (pe-ex1 e) (pe-ex1 f) 
  pe-ex1 (DAdd e f) = liftA2 EAdd (pe-ex1 e) (pe-ex1 f) 
  pe-ex1 (Lift e) = EInt <$> (pe-ex1 e)
  pe-ex1 (DLam {τ} e) = ELam  <$> pe-ex1 e
  -- Technical note: In the case for variables we can simply exploit
  -- the fact that variables are functorial in the actual type of
  -- their contexts' elements
  pe-ex1 (Var {D _} x) = just (EVar (mapIdx typeof x))
  pe-ex1 _ = nothing

  ex1-test : pe-ex1 ex1 ≡ just ex1-spec
  ex1-test = refl

  data Static : AType → Set where
    SInt : Static AInt
    SFun : ∀ { α₁ α₂ } → Static α₂ → Static (AFun α₁ α₂)

  is-static : (α : AType) → Dec (Static α)
  is-static α = {!!}

  Imp2 : Ctx → AType → Set
  Imp2 _ AInt = ℕ
  Imp2 Γ (D τ) = Exp Γ τ
  Imp2 Γ (AFun α₁ α₂) =   Imp2 Γ α₁ → Imp2 Γ α₂

-- The interpretation of annotated types. 
Imp : Ctx → AType → Set
Imp Γ (AInt) = ℕ
Imp Γ (AFun α₁ α₂) = ∀ {Γ'} → Γ ↝ Γ' → (Imp Γ' α₁ → Imp Γ' α₂)
Imp Γ (D σ) = Exp Γ σ


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

lift : ∀ {Γ Γ'} α → Γ ↝ Γ' → Imp Γ α → Imp Γ' α 
lift AInt p v = v
lift (AFun x x₁) Γ↝Γ' v = λ Γ'↝Γ'' → v (↝-trans Γ↝Γ' Γ'↝Γ'')
lift (D x₁) Γ↝Γ' v = elevate (↝↝-base Γ↝Γ') v

module SimpleAEnv where
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
  pe (Var x) env = lookup env x 
  pe (AInt x) env = x
  pe (AAdd e₁ e₂) env = pe e₁ env + pe e₂ env
  pe (ALam {α} e) env = λ Γ↝Γ' → λ y → pe e (cons α y (liftEnv Γ↝Γ' env)) 
  pe (AApp e₁ e₂) env = ((pe e₁ env) ↝-refl) (pe e₂ env)
  pe (DInt x) env = EInt x
  pe (DAdd e e₁) env = EAdd (pe e env) (pe e₁ env)
  pe (DLam {σ} e) env = ELam (pe e (consD σ env))
  pe (DApp e e₁) env = EApp (pe e env) (pe e₁ env)
  pe (Lift e) env = EInt (pe e env) 

module CheckExamples where
  open import Relation.Binary.PropositionalEquality hiding ([_])
  open SimpleAEnv 
  open AExp-Examples 

  check-ex1 : pe ex1 [] ≡ ex1-spec
  check-ex1 = refl

  check-ex0 : pe ex0 [] ≡ ex0-spec
  check-ex0 = refl

  check-ex0' : pe ex0' [] ≡ ex0'-spec
  check-ex0' = refl
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
  strip (AAdd e f) = EAdd (strip e) (strip f)
  strip (ALam e) = ELam (strip e)
  strip (AApp e f) = EApp (strip e) (strip f)
  strip (DInt x) = EInt x
  strip (DAdd e f) = EAdd (strip e) (strip f)
  strip (DLam e) = ELam (strip e)
  strip (DApp e f) = EApp (strip e) (strip f)
  strip (Lift e) = strip e

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
                  Γ↝Γ' ⊢ env ↝ env' →
                  Γ'↝Γ'' ⊢ env' ↝ env'' →
                  let Γ↝Γ'' = ↝-trans Γ↝Γ' Γ'↝Γ'' in
                  Γ↝Γ'' ⊢ env ↝ env'' 
    -- env↝trans {Γ} {.Γ''} {Γ''} {Γ↝Γ'} {.↝-refl} {env} {.env''} {env''} env↝env' (refl .env'') = env↝env'
    -- env↝trans env↝env' (extend v env'↝env'') = extend v (env↝trans env↝env' env'↝env'')

    -- TODO: why does this work???
    env↝trans {.Γ'} {Γ'} {Γ''} {.↝-refl} {Γ'↝Γ''} {.env'} {env'} (refl .env') env'↝env''
      rewrite sym (lem-↝-refl-id  Γ'↝Γ'') = env'↝env'' 
    env↝trans (extend v env↝env') env'↝env'' = env↝trans (extend v env↝env') env'↝env''

    -- Equivalent Imp Γ α and EImp τ values (where τ = stripα α). As
    -- (v : Imp Γ α) is not necessarily closed, equivalence is defined for
    -- the closure (Env Γ, ImpΓ α)
    Equiv : ∀ {α Γ} → Env Γ → Imp Γ α → EImp (stripα α) → Set 
    Equiv {AInt} env av v = av ≡ v
    Equiv {AFun α₁ α₂} {Γ} env af f = -- extensional equality, given -- an extended context
        ∀ {Γ' env' Γ↝Γ'} → (Γ↝Γ' ⊢ env ↝ env') →
        {ax : Imp Γ' α₁} → {x : EImp (stripα α₁)} →
        Equiv env' ax x → Equiv env' (af Γ↝Γ' ax) (f x)
    Equiv {D x} {Γ} env av v = ev av env ≡ v -- actually we mean extensional equality

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
              Equiv-Env env' (cons α va (aenv)) (v ∷ env)

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

    lem-elevate-≡ : ∀ {τ Γ Γ' Γ''}
                      {Γ↝Γ'↝Γ'' : Γ ↝ Γ' ↝ Γ''}
                      {env : Env Γ} {env' : Env Γ'} {env'' : Env Γ''} →
                      Γ↝Γ'↝Γ'' ⊢ env ↝ env' ↝ env'' ⊣ →
                      (e : Exp Γ τ) →
                      ev e env ≡ ev (elevate Γ↝Γ'↝Γ'' e) env''
    lem-elevate-≡ env↝env' (EVar x) = lookup-elevate2-≡ env↝env' x
    lem-elevate-≡ env↝env' (EInt x) = refl
    lem-elevate-≡ env↝env' (EAdd e f) with lem-elevate-≡ env↝env' e | lem-elevate-≡ env↝env' f
    ... | IA1 | IA2 = cong₂ _+_ IA1 IA2
    lem-elevate-≡ {Γ↝Γ'↝Γ'' = Γ↝Γ'↝Γ''}
                  {env = env}
                  {env'' = env''}
                  env↝env' (ELam e) = ext lem-elevate-≡-body
      where lem-elevate-≡-body : ∀ x → ev e (x ∷ env) ≡ ev (elevate (↝↝-extend Γ↝Γ'↝Γ'') e) (x ∷ env'')
            lem-elevate-≡-body x = lem-elevate-≡ (extend env↝env' x) e
    lem-elevate-≡ env↝env' (EApp e f) with lem-elevate-≡ env↝env' e | lem-elevate-≡ env↝env' f
    ... | IA1 | IA2 = cong₂ (λ f₁ x → f₁ x) IA1 IA2

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
    lem-lift-refl-id {D x} env v e eq rewrite sym eq = sym (lem-elevate-≡ (refl (refl env)) e) 

    
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
    lem-lift-equiv {D x} va v (extend v₁ env↝env') eq
      rewrite sym eq = sym (lem-elevate-≡ (refl (extend v₁ env↝env')) va)

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
    pe-correct (AAdd e f) env' eqenv
      rewrite pe-correct e env' eqenv | pe-correct f env' eqenv = refl
    pe-correct (ALam e) env' eqenv =
      λ {_} {env''} env'↝env'' {av'} {v'} eq →
        let eqenv' = (lem-equiv-env-lift-lift env'↝env'' eqenv)
            eqenv'' = (cons eqenv' av' v' eq)
        in pe-correct e env'' eqenv''
    pe-correct (AApp e f) env' eqenv
      with pe-correct e env' eqenv | pe-correct f env' eqenv
    ... | IAe | IAf = IAe (refl env') IAf
    pe-correct (DInt x) env' eqenv = refl
    pe-correct (DAdd e f) env' eqenv 
      rewrite pe-correct e env' eqenv | pe-correct f env' eqenv = refl
    pe-correct (DLam e) env' eqenv =
      ext (λ x → let eqenv' = (lem-equiv-env-lift-extend env' eqenv x)
                     eqenv'' = (cons eqenv' (EVar hd) x refl)
                 in pe-correct e (x ∷ env') eqenv'')
    pe-correct (DApp e f) {env = env} env' eqenv
      with pe-correct f env' eqenv | pe-correct e env' eqenv 
    ... | IA' | IA = cong₂ (λ f x → f x) IA IA'
    pe-correct (Lift e) env' eqenv
      with pe-correct e env' eqenv
    ... | IA = IA


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
