module Examples where

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

{-
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
  --ex1' : AExp [ AFun (D Int) (D Int) ] (D Int)
  --ex1' = AApp x (DInt 42)



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
  --ex3' : AExp [ AFun (AInt • (D Int)) (D Int) ] (D Int)
  --ex3' = AApp x (AInt 42 , DInt 42)
  
  -------------------
  -- b. Dynamic Pairs
  -------------------
  ex4 : AExp [] (D Int)
  ex4 = AApp (ALam (DSnd (Var hd))) ( DInt 43 ḋ DInt 42)  

  -- similar to ex1'
  --ex4' : AExp [ AFun (D (Int • Int)) (D Int) ] (D Int)
  --ex4' = AApp x (DInt 43 ḋ DInt 42)


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
  --ex1'-env : AEnv [ AFun (D Int) (D Int) ] 
  --ex1'-env = inp (ALam {[]} {D Int} (Var hd)) ∷ []


  -- Similarly, an environment like ex3'-env should be able to close ex3'
  -- and a partial evaluation of the closure should yield the same
  -- result as in example ex3:
  --ex3'-env : AEnv [ AFun (AInt • (D Int)) (D Int) ]
  --ex3'-env = inp (ALam {[]} {AInt • (D Int)} (Snd (Var hd))) ∷ []

  
  -- Also, an environment like ex4'-env should be able to close ex4'
  -- and a partial evaluation of the closure should yield the same
  -- result as in example ex4:
  --ex4'-env : AEnv [ AFun (D (Int • Int)) (D Int) ]
  --ex4'-env = inp (ALam {[]} {D (Int • Int)} (DSnd (Var hd))) ∷ []  
  
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
  
-}

{-

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

-}

