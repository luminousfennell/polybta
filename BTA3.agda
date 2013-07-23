module BTA3 where

open import Data.Nat
open import Data.Bool
open import Data.List

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

-- note that the above function can also be specified as follows,
-- _≼_ : BT → BT → Bool 
-- D ≼ S = false
-- _ ≼ _ = true

-- note that the function [≼] specifies that a "static",S, can be treated
-- as a "dynamic",D, and not the other way round
-- since in Agda, pattern matching is conducted in a sequencial fashion,
-- the above specification makes sure that it returns [false] when the 
-- first argument is [D] and the second [S] and returns [true] in all
-- the other three cases.




-- BEGIN: stuff that is also in the standard library

-- Standard propositional equality, see also Relation.Binary.PropositionalEquality
data _==_ {A : Set} (x : A) : A → Set where
  refl : x == x
-- [_==_] defines an equality proposition
-- it takes two identical elements of one type as arguments and gives one 
-- evidence,[refl],for the proposition

-- subst lemma
subst : {A B : Set}{x x' : A} {C : A → B} → x == x' → C x == C x'
subst{A}{B}{x}{.x} refl = refl

-- or being defined in the following manner...
-- my_subst : {A B : Set}{x x' : A}{C : A → B} →  x == x' → C x == C x'
-- my_subst refl = refl

-- the above function further helps to construct evidence for equality 
-- proposition
-- it says that if two elements are identical then two new elements obtained
-- by applying the former to a function  should also be identical



record True : Set where
data False : Set where

-- note that the above is regarding two simple proposition [True] and [False]
-- regarding [True],
-- it is defined as empty record with a single element of type [True],[record{}]
-- the trick here is that the type checker knows this and fills in any implicit
-- arguments of [True] with this element
-- another way of defining [True] as follows,
-- record True : Set where
-- trivial : True
-- trivial = _

-- regarding [False],
-- it is defined as a proposition without any evidence corresponding well to
-- what a [False] proposition really means

isTrue : Bool → Set
isTrue true  = True
isTrue false = False
-- note the isTrue b,given b as boolean, is the type of proof that b is equal to
-- true since if it is the case, [isTrue b] returns type [True] where its
-- evidence is automatically filled in by the type checker while if it is not
-- the case there is no way to supply for the evidence due to the way how 
-- [false] is constructed 


-- END standard library

-- some lemmas about BT subsumption
lem-bt≼S : {bt : BT} → isTrue (bt ≼ S) → bt == S
lem-bt≼S {S} bt≼S = refl
lem-bt≼S {D} ()

-- which can also be defined as follows,
-- my_lem-bt≼S : {bt : BT} → isTrue (bt ≼ S) → bt == S
-- my_lem-bt≼S {S} _ = refl
-- my_lem-bt≼S {D} ()

lem-D≼bt : {bt : BT} → isTrue (D ≼ bt) → bt == D
lem-D≼bt {S} ()
lem-D≼bt {D} D≼bt = refl

-- which can also be defined as follows,
-- my_lem-D≼S : {bt : BT} → isTrue (D ≼ bt) → bt == D
-- my_lem-D≼S {S} ()
-- my_lem-D≼S {D} _ = refl

-- note that the above two functions help us to determine whether
-- the element of concern is dynamic [D] or static [S]
-- if it is the case then it returns an evidence of the equality

-- also note that the above cases examplify the benefit of defining [True] as
-- record type,
-- since the type checker will fill in the sole element of the type for us 
-- we can write intuitive notations in such places to improve readability

-- Types of the calculus
mutual
  -- s ^ BT
  data AType : Set where
    Ann : BT → SType → AType

  -- int | t -> t
  data SType : Set where
    SInt  : SType
    SFun  : AType → AType → SType

-- the above definition of types consists of,
-- a. the ground types,[SType],which consists of 
--    integer [SInt] which is not annotated
--    and
--    function [SFun] whose arguments are annotated(of type [AType])
-- b. the annotated types,[AType], which is constructed from an element
--    of [BT] standing for the annotation and an element of [SType]

-- some example types and their corresponding representation according
-- to the above definition,
-- int^{S} int^{D} int^{S}→int^{D} (int^{S}→int^{D})^{S}
-- Ann S SInt
-- Ann D SInt
-- SFun (Ann S SInt) (Ann D SInt)
-- Ann S (
--         SFun (Ann S SInt) (Ann D SInt)
--       )

-- aux definitions
ATInt : BT → AType
ATInt bt = Ann bt SInt
ATFun  : BT → AType → AType → AType
ATFun  bt at1 at2 = Ann bt (SFun at1 at2)

-- note that the above function labels a ground type with annotations [S] or
-- [D],sort of a labelling function

-- projection: get the BT from a type
btof : AType → BT
btof (Ann bt _) = bt

-- a related function which takes an annotated type as argument and returns
-- the annotation of that type

-- "constraint on types: functions have to be at least as dynamic as their component" should be corrected as follows,
-- arguments of function should be as dynamic as the function

data wft : AType → Set where
  wf-int  : ∀ {bt} → wft (Ann bt SInt)
  wf-fun  : ∀ {bt at1 at2} → wft at1 → wft at2
          → isTrue (bt ≼ btof at1) → isTrue (bt ≼ btof at2) → wft (Ann bt (SFun at1 at2))

-- the above proposition specifies a set of well-formed [AType]s,
-- any annotated [SInt]s are well-formed, wft (Ann bt SInt) forall bt ∈ BT
-- in case of functional type with annotation, the following two criteria have
-- to be satisfied to be a well form,
-- a. each of its arguments is well-formed
-- b. the annotation of the function and the annotations of its arguments must
--    satisfy [_≼_] relation
--    for instance, the functional type defined above is well-formed while
--    the following is not,
--    Ann D (
--            SFun (Ann S SInt) (Ann D SInt)
--          )
--    in conclusion,for functional type with annotation to be well-formed,
--    each of its arguments annotations has to be [D] when that of the function
--    is [D] while there is no constraint upon the annotations of its arguments
--    when that of the function is [S]

lem-force-bt : ∀ {bt at} → isTrue (bt ≼ btof at) → D == bt → D == btof at
lem-force-bt {S} bt≼at ()
lem-force-bt {D} {Ann S y'} () D=bt
lem-force-bt {D} {Ann D y'} bt≼at D=bt = refl

-- note the above function takes an element[bt] of type [BT] and a type with 
-- annotation,
-- if both 
-- a. the type is at least as dynamic as [bt]
-- b. [bt == D]
-- then we know that the annotation of the type must be [D] as well
-- and the function in that case returns evidence for that

-- Low-level types; types wihtout binding information
data Type : Set where
  TInt : Type
  TFun : Type → Type → Type

-- translation from ATypes to low-level types
mutual
  strip : AType → Type
  strip (Ann _ σ) = strip' σ

  strip' : SType → Type
  strip' SInt = TInt
  strip' (SFun y y') = TFun (strip y) (strip y')

-- note that the above function [strip] converts a type with annotation [AType]
-- to a low-level type [Type],
-- for instance,
-- strip (Ann D SInt)
-- = strip' SInt
-- = TInt
-- strip (Ann S
--         SFun (Ann S SInt) (Ann D SInt)
--       )
-- = strip' (SFun (Ann S SInt) (Ann D SInt))
-- = TFun (strip (Ann S SInt)) (strip (Ann D SInt))
-- = TFun (strip' SInt) (strip' SInt) 
-- = TFun TInt TInt^

-- More general purpose definitions (should also be in standard library)
-- list membership
infix 4 _∈_
data _∈_ {A : Set} : A → List A → Set where
  hd : ∀ {x xs} → x ∈ (x ∷ xs)
  tl : ∀ {x y xs} → x ∈ xs → x ∈ (y ∷ xs)

-- note the above proposition gives us two constructors for getting
-- evidences for an element being a member of one list 

-- end general purpose definitions 

-- Typing context
Ctx = List Type

--data Exp' (Γ Γ' : Ctx) : Type → Set where
--  EVar' : 

-- Typed expression
data Exp (Γ : Ctx) : Type → Set where
  -- [EVar] corresponds to the bounded variables in [AExp]
  EVar : ∀ {τ} → τ ∈ Γ → Exp Γ τ
  EInt : ℕ → Exp Γ TInt
  EFun : ∀ {τ₁ τ₂} → Exp (τ₂ ∷ Γ) τ₁ → Exp Γ (TFun τ₂ τ₁)
  EApp : ∀ {τ₁ τ₂} → Exp Γ (TFun τ₂ τ₁) → Exp Γ τ₂ → Exp Γ τ₁
-- one additional term,

-- EDummy : ∀ {τ} → Exp Γ τ

-- note given a context of low-level types, we are ready to specify 
-- well-typed low-level expressions,
-- a. [EVar y : Exp gamma τ] if variable y has type τ given gamma
--    note that since y is actually an evidence for [τ ∈ gamma],
--    it actually has the form [tl tl ... tl hd] where the number
--    of tl's and hd corresponds to the index of the element on the list
--    which is the type of the variable
--    in fact we can actually construct a function which would give us
--    the type of a variable given a context
-- b. [EInt ℕ : Exp gamma TInt]
-- c. [EFun e : Exp gamma (TFun τ₂ τ₁)] where e is an expression of type,
--    [e : Exp (τ₂::gamma) τ₁]
--    note that e here as the function body should have type τ₁ given 
--    the input of type τ₂
-- d. [EApp e₁ e₂ : Exp gamma τ₂] where e₁ and e₂ have the following types,
--    [e₁ : Exp gamma (TFun τ₁ τ₂)] and [e₂ : Exp gamma τ₁]

-- typed annotated expressions

ACtx = List AType

data AExp' (△ △' : ACtx) : AType → Set where
  AVar'  : ∀ {α}   → α ∈ △  → AExp' △ △' α
  ABvar' : ∀ {α}   → α ∈ △' → AExp' △ △' α
  AInt'  : (bt : BT) →    ℕ      → AExp' △ △' (ATInt bt)
  AFun'  : ∀ {α₁ α₂} (bt : BT) → wft (ATFun bt α₂ α₁) → AExp' △ (α₂ ∷ △') α₁ → AExp' △ △' (ATFun bt α₂ α₁)
  AApp'  : ∀ {α₁ α₂} (bt : BT) → wft (ATFun bt α₂ α₁) → AExp' △ △' (ATFun bt α₂ α₁) → AExp' △ △' α₂ → AExp' △ △' α₁ 

-- note that [AExp'] carries two typing contexts,
-- one is our good-old typing context for free variables and
-- the other is that for bounded variables


data AExp (Δ : ACtx) : AType → Set where
 -- free variables,
  AVar : ∀ {α} → α ∈ Δ → AExp Δ α
 -- note that it seems to be necessary to distinguish between
 -- Bounded variables,
 -- ABvar : ∀ {α₁ α₂} → α₁ ∈ (α₂ ∷ Δ) → AExp Δ α₁
 -- bounded variables and unbounded variables 
 -- to be visited later...
  AInt : (bt : BT) → ℕ → AExp Δ (ATInt bt)
  AFun : ∀ {α₁ α₂} (bt : BT) → wft (ATFun bt α₂ α₁) → AExp (α₂ ∷ Δ) α₁ → AExp Δ (ATFun bt α₂ α₁)
  AApp : ∀ {α₁ α₂} (bt : BT) → wft (ATFun bt α₂ α₁) → AExp Δ (ATFun bt α₂ α₁) → AExp Δ α₂ → AExp Δ α₁

  -- since a well-typed function implies that the function is well-formed so
  -- [AApp] can be rewritten as follows,
  -- : ∀ {α₁ α₂}(bt : BT) → AExp △ (ATFun bt α₂ α₁) → AExp △ α₂
  --     → AExp △ α₁

-- now in case of annotated types, we also have to make sure that all the
-- annotations of a type are consistent with each other. For instance, in
-- case of function types we have to make sure that the arguments are at least
-- as dynamic as the function itself
-- again we have,
-- a. [AVar y : AExp gamma τ] where τ is the type of y according to gamma
-- b. [AInt bt n : AExp gamma (Ann bt SInt)]
-- c. [AFun bt e₁ e₂ : AExp gamma (Ann bt (SFun τ₁ τ₂))] where
--    e₁ is the evidence that the annotations of the function type are 
--    consistent and e₂ has the following type,
--    [e₂ : AExp (τ₁::gamma) τ₂]
-- d. [AApp bt e₁ e₂ e₃ : AExp gamma τ₃] with
--    e₁ as the evidence of well-formed function type and
--    [e₂ : AExp gamma (Ann bt (SFun τ₂ τ₃))] and [e₃ : AExp gamma τ₂]



-- stripping of contexts
residual : ACtx → Ctx
residual [] = []
residual (Ann S _ ∷ xs) = residual xs
residual (Ann D σ ∷ xs) = strip' σ ∷ residual xs

-- another way of converting one environment to another,
-- residual' : ACtx → Ctx
-- residual' [] = []
-- residual' (Ann _ α ∷ xs ) = strip' α ∷ residual' xs

-- note the above function converts a list of annotated types to a list of
-- low-level types in the following way,
-- it skips all static types on the list and strip off the annotations of
-- dynamic types to obtain the corresponding low-level types
-- consider the following list of annotated types,
-- (Ann S SInt)::(Ann D SInt)::(Ann D (SFun (Ann D SInt) (Ann D SInt)))
-- use [residual] we can convert it to a list of low-level types,
-- TInt::(TFun TInt TInt)
mutual 
  ImpTA : Ctx → ACtx → AType → Set
  ImpTA Γ Δ (Ann S σ) = ImpTA' Γ Δ σ
  ImpTA Γ Δ (Ann D σ) = Exp Γ (strip' σ)
  
  ImpTA' : Ctx → ACtx → SType → Set
  ImpTA' Γ Δ SInt = ℕ
  ImpTA' Γ Δ (SFun y y') = ImpTA Γ Δ y → ImpTA Γ Δ y'

-- note modify the above [ImpTA] as follows,
mutual
  impta  : Ctx → ACtx → AType → Set
  impta Γ Δ (Ann S σ)   = impta' [] Δ σ
  impta Γ Δ (Ann D σ) = Exp Γ (strip' σ)

  impta' : Ctx → ACtx → SType → Set
  impta' Γ Δ SInt = ℕ
  impta' Γ Δ (SFun y y') = impta Γ Δ y → impta Γ Δ y'

-- mutual
--   ImpTA : ACtx → AType → Set
--   ImpTA Δ (Ann S σ) = ImpTA' Δ σ
--   ImpTA Δ (Ann D σ) = Exp (residual Δ) (strip' σ)
  -- in [residual] using a different typing context,
  -- say Γ.

--   ImpTA' : ACtx → SType → Set
--   ImpTA' Δ SInt = ℕ
--   ImpTA' Δ (SFun y y') = ImpTA Δ y → ImpTA Δ y'


-- first off let us consider the following examples,
-- a. ImpTA gamma (Ann D SInt)
--    = Exp (residual gamma) TInt
-- b. ImpTA gamma (Ann S SInt)
--    = ImpTA' gamma SInt
--    = ℕ
-- c. ImpTA gamma (Ann S
--                  SFun (Ann S SInt) (Ann D SInt)
--                )
--    = ImpTA' gamma (SFun (Ann S SInt)(Ann D SInt))
--    = ImpTA gamma (Ann S SInt) → ImpTA gamma (Ann D SInt)
--    = ImpTA' gamma SInt →  Exp (residual gamma) TInt
--    = ℕ  -> Exp (residual gamma) TInt
-- from the above instances, we conclude that [ImpTA],
-- with the typing context [ACtx], and
-- 1. a static annotated type returns either [ℕ] or a function type
--    [τ₁ → τ₂] where [τ₁] and [τ₂] are again determined by
--    the typing context and whether the annotationis static or dynamic
-- 2. a dynamic annotated type returns a type of low-level expressions,
--    [Exp (residual gamma) (strip'τ)]

-- the following block is subject to modification...
-- to be modified...



-- data AEnv : ACtx → Set where
--  env[] : AEnv []
--  env:: : ∀ {Δ} {α : AType} → ImpTA (α ∷ Δ) α → AEnv Δ → AEnv (α ∷ Δ)


data AEnv : Ctx → ACtx → Set where
  env[] :  ∀{Γ} → AEnv Γ []
  envS:: : ∀ {Γ Δ} {α : SType} → ImpTA Γ (Ann S α ∷ Δ) (Ann S α) → AEnv Γ Δ → AEnv Γ (Ann S α ∷ Δ)
  envD:: : ∀ {Γ Δ} {α : SType} → ImpTA ((strip' α) ∷ Γ) (Ann D α ∷ Δ) (Ann D α) → AEnv ((strip' α) ∷ Γ) Δ → AEnv ((strip' α) ∷ Γ) (Ann D α ∷ Δ)

-- modify the above [AEnv] as follows,

data aenv' : Ctx → ACtx → Set where
  Env[]' : ∀{Γ} → aenv' Γ []
  Env::' : ∀{Γ Δ} {α : SType} {bt : BT} → impta Γ (Ann bt α ∷ Δ ) (Ann bt α) → aenv' Γ Δ → aenv' Γ (Ann bt α ∷ Δ)

data aenv  : Ctx → ACtx → Set where
  Env[]  : ∀{Γ} → aenv Γ []
  EnvD:: : ∀{Γ Δ} {α : SType} → impta ((strip' α) ∷ Γ) (Ann D α ∷ Δ) (Ann D α) → aenv' ((strip' α) ∷ Γ) Δ → aenv ((strip' α) ∷ Γ) (Ann D α ∷ Δ)
  EnvS:: : ∀{Γ Δ} {α : SType} → impta Γ (Ann S α ∷ Δ) (Ann S α) → aenv Γ Δ → aenv Γ (Ann S α ∷ Δ)

-- note that the above definition is created to account for cases where
-- we need to rewrite some of the values in the form [EVar y] to the form
-- [EVar tl y]

-- now we write a function to do such rewriting depending upon the new value
-- being created is dynamic or static


Dextend' : ∀ {Γ Δ} {α : Type} → aenv' Γ Δ → aenv' (α ∷ Γ) Δ
Dextend' Env[]' = Env[]'
Dextend' (Env::' {bt = D} (EVar y) env) = Env::' {bt = D} (EVar (tl y)) (Dextend' env)
Dextend' (Env::' x env) = Env::' x (Dextend' env)
 
Dextend : ∀ {Γ Δ} {α : Type} → aenv Γ Δ  → aenv' (α ∷ Γ) Δ 
Dextend  Env[]               = Env[]'
Dextend (EnvS:: x env)       = Env::' x (Dextend env)
Dextend (EnvD:: (EVar y) Env[]') = Env::' (EVar (tl y)) Env[]'
Dextend (Env::' (EVar y) Env[]') = Env::' (EVar (tl y)) Env[]'
Dextend (EnvD:: (EVar y) env)    = Env::' (EVar (tl y)) (Dextend env)
Dextend (envD:: y env) = envD:: y (Dextend env)  

-- Aextend :  ∀ {Δ}{α : SType} → ImpTA (Ann D α ∷ Δ) (Ann D α) → AEnv Δ → AEnv (Ann D α ∷ Δ)
--Aextend x env = env:: x {!!}

-- considering that all terms in the value context are closed terms
-- we need to redefine [AEnv] as follows,
-- data AEnv' : ACtx → Set where
--  env[]' : AEnv' []
--  env::' : ∀ {△} {α : AType} → ImpTA [] α → AEnv' △ → AEnv' (α ∷ △)

  -- in case of bounded variables, the typing context is extended without
  -- extending the value context
  -- env** : ∀ {Δ} {α : AType} → AEnv Δ → AEnv (α ∷ Δ)

-- note that a similar construction in Lu's file as follows,
-- data Env : ∀ {n} → Ctxt n → Set where
--   []   : Env []
--   _::_ : ∀ {n t} → (v : eval-ty t) → {Γ : ctxt n} → (env : Env Γ)
--          → Env (t :: Γ)
-- the difference between these two are that the latter when taking a value
-- as input, the calculation of the type of the value is independent from
-- the typing context, which is obvious for by definition value terms do
-- not have free variables
-- by contrast, the calculation of the type of the value in [AEnv] has to
-- include the typing context for depending upon the structure and annotation
-- of [α], the result could also be the type of the low-level term which 
-- can contain free variables

-- however, both approches observe the "one-to-one correspondance" between
-- the typing context and the value context 




-- note that [AEnv] not only specifies how the "value context" is being
-- constructed, it also establishes the correspondance between "typing context"
-- and the "value context"

--lookup₁ : ∀ { △ : ACtx }{α : AType}  → α ∈ △ → ACtx
--lookup₁ {[]} ()
--lookup₁ {x ∷ xs}  hd  = x ∷ xs 
--lookup₁ {x ∷ xs} (tl y) = lookup₁ {xs} y

--lookup : ∀ {Δ : ACtx}{α : AType} → AEnv Δ → (o : α ∈ Δ ) → ImpTA (lookup₁ o) α
--lookup  (env[]) ()
--lookup  (env:: y y') hd = y --{!!}
--lookup  (env:: y' y0) (tl y1) = lookup y0 y1 -- lookup y0 y1 --{!!}

-- a note to be added here...

-- extract : ∀ {△ : ACtx}{α : AType} → AExp △ α → ACtx
-- extract (AVar y) = lookup₁ y
-- extract {△} _        = △ 

-- 
-- data Case : Set where
-- c1 : ∀ {△ : ACtx}{α : AType} → α ∈ △ → Case -- [AVar]
--  c2 : ∀ (n : ℕ) →  Case -- [AInt]
--  c3 : Case -- [AFun]
--  c4 : Case -- [AApp]

-- case : ∀ {△ : ACtx}{α : AType} → (e : AExp △ α) → Case
-- case (AVar y) = c1 y
-- case (AInt _ y) = c2 y
-- case (AFun _ y y') = c3
-- case (AApp _ y y' y0) = c4
 
-- pe₁ : ∀ {Δ : ACtx}{α₁ α₂ : AType} → AEnv Δ → (e : AExp Δ (Ann D (SFun α₂ α₁))) → ImpTA Δ (Ann D (SFun α₂ α₁))
-- pe₁ env (AFun .D y y') with case y'
-- pe₁ env (AFun .D y y') | c1 hd = EFun (EVar hd)
-- pe₁ env (AFun .D y y') | c1 (tl z') = EFun (EVar (tl z'))
-- pe₁ env (AFun .D y y') | c2 n = EFun (EInt n)

 
-- partial evaluation
pe : ∀ {Γ : Ctx}{Δ : ACtx}{α : AType} →   AEnv Γ Δ → (e : AExp Δ α) → ImpTA Γ Δ α
-- pe : ∀ {Δ : ACtx}{α : AType} → AEnv Δ → (e : AExp Δ α) → ImpTA Δ α
-- bounded variables,
-- pe  env (ABvar y) = {}
-- free variables,
pe  env (AVar y)= {!!} -- lookup env y  --lookup env y --{!!}
-- the case of variable needs to be reconsidered
pe  env (AInt S y) = y
pe  env (AInt D y) = EInt y

-- Lu's idea,
-- pe  env (AFun D y y') = EFun (pe ((EVar hd) ∷ env) y')
-- pe  [] (AFun D y (AFun D y AVar tl hd)) =>
-- pe  [EVar hd] (AFun D y AVar tl hd)     =>
-- pe  [EVar hd,EVar tl hd] (AVar tl hd)
-- end of Lu's idea
-- note Lu's idea is not going to work
-- consider the following example,
-- pe env[] (AFun D e-wf (AVar hd))
-- what we would like to have is the following evaluation sequence,
-- pe env[] (AFun D e-wf (AVar hd)) =>
-- EFun (pe env:: EVar hd env[] AVar hd) =>
-- EFun (EVar hd)
-- however we can show that the above evaluation sequence cannot be 
-- obtained,
--  ^^^^^^-- Suppose that [AVar hd : AExp (Ann D AInt) (Ann D AInt)] and we have
-- [AFun D e-wf AVar hd : AExp [] (ATFun D (Ann D SInt)(Ann D SInt))]
-- and from which we can get the type of the resulting  expression as
-- ImpTA [] (ATFun D (Ann D SInt)(Ann D SInt)) = Exp [] (TFun TInt TInt)
-- now let us consider the type of [pe env:: EVar hd env[] AVar hd]
-- note that the type of [AVar hd] as [AExp [Ann D SInt] (Ann D SInt)] and
-- we have to construct a [AEnv (Ann D SInt)] which is [env:: EVar hd env[]]
-- according to [env::]; [EVar hd] has to have type [ImpTA [] (Ann D SInt)]
-- which is [Exp [] TInt], it is obvious that this is impossible,for variables
-- are not typable under empty context, so Lu's idea is not working. Qed.


-- pe  env (AFun D y (.(AVar z))) | (AVar z) with z
-- pe  env (AFun D y (.(AVar hd))) | (AVar z) | hd = EFun (EVar hd)
-- note that the above specification only works if all types in [△]
-- are dynamic so that the position of type on the new typing environment
-- corresponds to exactly the position of type on the old one

-- this problem,however,can be fixed with a simple modification of the
-- [residual] function. See [residual'] 
-- pe  env (AFun D y (.(AVar (tl z')))) | (AVar z) | tl z' = EFun (pe env (AVar z'))

pe  env (AFun D y y') = {! EFun (pe (envD:: (EVar hd)))!} -- EFun (pe (env:: (EVar hd) {!!}) {!!}) -- EFun (pe (env:: (EDummy) env) y' )  -- {!!}
-- [with] method should be used here to do pattern matching
pe  env (AFun S y y') = {!!}--λ x → pe (env:: x env) y' --{!!}


-- note that,
-- y : wft (ATFun bt α₂ α₁)
-- y': AExp (α₂ :: △) α₁
-- △ should not be changed
pe  env (AApp S y y' y0) = {!!} -- (pe env y') (pe env y0) -- {!!}
pe  env (AApp D y y' y0) = {!!}--EApp (pe env y') (pe env y0)  -- {!!}

-- end of the block
-- let us suppose that we always have a fixed typing context to begin with,
-- [△ : ACtx]

-- data my_AEnv : ACtx → ACtx → Set where
--   my_env[] : ∀ {Δ} →  my_AEnv Δ []
--   my_env:: : ∀ {Δ Δ'}{α : AType} → ImpTA Δ α → my_AEnv Δ Δ' → my_AEnv Δ  (α ∷ Δ')

-- my_lookup : ∀ {Δ Δ' : ACtx}{α : AType} → my_AEnv Δ Δ' → (α ∈ Δ') → ImpTA Δ α
-- my_lookup (my_env[]) ()
-- my_lookup (my_env:: y y') hd = y
-- my_lookup (my_env:: y' y0) (tl y1) = my_lookup y0 y1 

-- my partial evaluation

-- my_pe : ∀ {Δ : ACtx}{α : AType} → my_AEnv Δ Δ  → AExp Δ α → ImpTA Δ α
-- my_pe env (AVar y) = my_lookup env y
-- my_pe env (AInt S y) = y
-- my_pe env (AInt D y) = EInt y
-- my_pe env (AFun bgt y y') = {!!}
-- my_pe env (AApp bt y y' y0) = {!!}
