\agdaIgnore{
\begin{code}
module TwoLevelAnnotations where
open import Lib
open import BaseFull
open import TwoLevelFull

\end{code}}
\agdaSnippet\btaDefinition{
\begin{code}
data BT : Set where
  S : BT
  D : BT
\end{code}}
\agdaIgnore{
-- Ordering on binding times: dynamic binding time subsumes static
-- binding time.
}
\agdaSnippet\btaOrdering{
\begin{code}
data _⊑_ : BT → BT → Set where
  S⊑S : S ⊑ S
  S⊑D : S ⊑ D
  D⊑D : D ⊑ D
\end{code}}
\agdaSnippet\btaATypeBType{
\begin{code}
mutual
  data AType' : Set where
    an  : BT → BType → AType'
   
  data BType : Set where
    BNum : BType
    BFun : AType' → AType' → BType
    BPrd : AType' → AType' → BType 
    BSum : AType' → AType' → BType 
\end{code}}
\agdaSnippet\btaATypeWft{
\begin{code}
_≼_ : BT → AType' → Set
β ≼ an β₁ _ = β ⊑ β₁

data wft : AType' → Set where
  wf-num : ∀ {β} → wft (an β BNum)
  wf-fun : ∀ {β} {α₁ α₂} → wft α₁ → wft α₂ 
           → β ≼ α₁ → β ≼ α₂ → wft (an β (BFun α₁ α₂))
  wf-prd : ∀ {β} {α₁ α₂} → wft α₁ → wft α₂ 
           → β ≼ α₁ → β ≼ α₂ → wft (an β (BPrd α₁ α₂))  
  wf-sum : ∀ {β} {α₁ α₂} → wft α₁ → wft α₂ 
           → β ≼ α₁ → β ≼ α₂ → wft (an β (BSum α₁ α₂))
\end{code}}
\agdaIgnore{
\begin{code}
lem-S-≼ : ∀ α' → S ≼ α'
lem-S-≼ (an S x₁) = S⊑S
lem-S-≼ (an D x₁) = S⊑D

tToWft : Type → Σ AType' (λ α → wft α × D ≼ α)
tToWft Num = an D BNum , wf-num , D⊑D
tToWft (Fun τ τ₁) with tToWft τ | tToWft τ₁ 
... | tw | tw₁ = an D (BFun (proj₁ tw) (proj₁ tw₁)) , wf-fun (proj₁ (proj₂ tw)) (proj₁ (proj₂ tw₁)) (proj₂ (proj₂ tw)) (proj₂ (proj₂ tw₁)) , D⊑D
tToWft (Prd τ τ₁) with tToWft τ | tToWft τ₁ 
tToWft (Prd τ τ₁) | t , w , p | t₁ , w₁ , p₁ = an D (BPrd t t₁) , wf-prd w w₁ p p₁ , D⊑D
tToWft (Sum τ τ₁) with tToWft τ | tToWft τ₁ 
tToWft (Sum τ τ₁) | t , w , p | t₁ , w₁ , p₁ = an D (BSum t t₁) , wf-sum w w₁ p p₁ , D⊑D

wftTot : (α : AType') → wft α → D ≼ α → Type
wftTot (an S t) w ()
wftTot (an D BNum) w p = Num
wftTot (an D (BFun x x₁)) (wf-fun w w₁ x₂ x₃) (p) with wftTot x w x₂ | wftTot x₁  w₁  x₃
... | τ | τ₁ = Fun τ τ₁
wftTot (an D (BPrd x x₁)) (wf-prd w w₁ x₂ x₃) p with wftTot x w x₂ | wftTot x₁  w₁ x₃
... | τ | τ₁ = Prd τ τ₁
wftTot (an D (BSum x x₁)) (wf-sum w w₁ x₂ x₃) (p) with wftTot x w x₂ | wftTot x₁ w₁ x₃
... | τ | τ₁ = Sum τ τ₁

wftTot' : Σ AType' (λ α → wft α × D ≼ α) → Type
wftTot' (x , w , le) = wftTot x w le

lem-tToWft-dyn : (τ : Type) → ∃ λ bt → ∃ λ w → tToWft τ ≡ (an D bt , w , D⊑D) 
lem-tToWft-dyn Num = BNum , wf-num , refl
lem-tToWft-dyn (Fun τ τ₁) with lem-tToWft-dyn τ | lem-tToWft-dyn τ₁ 
lem-tToWft-dyn (Fun τ τ₁) | bt , w , p | bt₁ , w₁ , p₁ rewrite p | p₁ = BFun (an D bt) (an D bt₁) , wf-fun w w₁ D⊑D D⊑D , refl
lem-tToWft-dyn (Prd τ τ₁) with lem-tToWft-dyn τ | lem-tToWft-dyn τ₁ 
lem-tToWft-dyn (Prd τ τ₁) | bt , w , p | bt₁ , w₁ , p₁ rewrite p | p₁ = BPrd (an D bt) (an D bt₁) , wf-prd w w₁ D⊑D D⊑D , refl
lem-tToWft-dyn (Sum τ τ₁) with lem-tToWft-dyn τ | lem-tToWft-dyn τ₁ 
lem-tToWft-dyn (Sum τ τ₁) | bt , w , p | bt₁ , w₁ , p₁ rewrite p | p₁ = BSum (an D bt) (an D bt₁) , wf-sum w w₁ D⊑D D⊑D , refl

lem-iso-left-dyn : ∀ τ → wftTot' (tToWft τ) ≡ τ
lem-iso-left-dyn Num = refl
lem-iso-left-dyn (Fun τ τ₁) rewrite lem-iso-left-dyn τ | lem-iso-left-dyn τ₁ = refl
lem-iso-left-dyn (Prd τ τ₁) rewrite lem-iso-left-dyn τ | lem-iso-left-dyn τ₁ = refl
lem-iso-left-dyn (Sum τ τ₁) rewrite lem-iso-left-dyn τ | lem-iso-left-dyn τ₁ = refl

lem-iso-right-dyn : ∀ x w le → tToWft (wftTot' (x , w , le) ) ≡ (x , w , le)
lem-iso-right-dyn (an S x₁) w ()
lem-iso-right-dyn (an D BNum) wf-num D⊑D = refl
lem-iso-right-dyn (an D (BFun x x₁)) (wf-fun w w₁ p p₁) D⊑D
  rewrite lem-iso-right-dyn x w p | lem-iso-right-dyn x₁ w₁ p₁ = refl
lem-iso-right-dyn (an D (BPrd x x₁)) (wf-prd w w₁ p p₁) D⊑D
  rewrite lem-iso-right-dyn x w p | lem-iso-right-dyn x₁ w₁ p₁ = refl
lem-iso-right-dyn (an D (BSum x x₁)) (wf-sum w w₁ p p₁) D⊑D
  rewrite lem-iso-right-dyn x w p | lem-iso-right-dyn x₁ w₁ p₁ = refl
\end{code}}
\agdaSnippet\btaATypeIso{
\begin{code}
atToWft : AType → Σ AType' wft
wftToAt : Σ AType' wft → AType

lem-iso-left : ∀ α → wftToAt (atToWft α) ≡ α
lem-iso-right : ∀ α' → (w : wft α') →
        proj₁ (atToWft (wftToAt (α' , w))) ≡ α'
\end{code}}
\agdaIgnore{
\begin{code}
--
atToWft SNum = an S BNum , wf-num
atToWft (SFun at at₁) with atToWft at | atToWft at₁
... | aw | aw₁ = an S (BFun (proj₁ aw) (proj₁ aw₁)) , wf-fun (proj₂ aw) (proj₂ aw₁) (lem-S-≼ _) (lem-S-≼ _)
atToWft (SPrd at at₁) with atToWft at | atToWft at₁
atToWft (SPrd at at₁) | proj₁ , proj₂ | proj₃ , proj₄ = an S (BPrd proj₁ proj₃) , wf-prd proj₂ proj₄ (lem-S-≼ _) (lem-S-≼ _)
atToWft (SSum at at₁) with atToWft at | atToWft at₁
atToWft (SSum at at₁) | proj₁ , proj₂ | proj₃ , proj₄ = an S (BSum proj₁ proj₃) , wf-sum proj₂ proj₄ (lem-S-≼ _) (lem-S-≼ _)
atToWft (D x) with tToWft x 
... | tw = proj₁ tw , proj₁ (proj₂ tw)

--
wftToAt (an S BNum , w) = SNum
wftToAt (an S (BFun x x₁) , wf-fun w w₁ x₂ x₃) with wftToAt (x , w) | wftToAt (x₁ , w₁)
... | α | α₁ = SFun α α₁
wftToAt (an S (BPrd x x₁) , wf-prd w w₁ x₂ x₃) with wftToAt (x , w) | wftToAt (x₁ , w₁)
... | α | α₁  = SPrd  α  α₁
wftToAt (an S (BSum x x₁) , wf-sum w w₁ x₂ x₃) with wftToAt (x , w) | wftToAt (x₁ , w₁)
... | α | α₁ = SSum α α₁
wftToAt (an D at' , w) = D (wftTot' (an D at' , w , D⊑D))

-- TODO: ../BTA10.lagda contains a complete proof for the type
-- isomorpisms. It needs to be refactored to fit the definitions/names
-- used in the paper.
lem-iso-left SNum = refl
lem-iso-left (SFun α α₁) rewrite lem-iso-left α | lem-iso-left α₁ = refl
lem-iso-left (SPrd α α₁) rewrite lem-iso-left α | lem-iso-left α₁ = refl -- refl
lem-iso-left (SSum α α₁) rewrite lem-iso-left α | lem-iso-left α₁ = refl
lem-iso-left (D τ) with lem-tToWft-dyn τ 
lem-iso-left (D τ) | bt , w , p rewrite lem-iso-left-dyn τ | p = {! !}

lem-iso-right (an S BNum) wf-num = refl
lem-iso-right (an S (BFun x x₁)) (wf-fun w w₁ x₂ x₃)
  rewrite lem-iso-right x w | lem-iso-right x₁ w₁ = refl
lem-iso-right (an S (BPrd x x₁)) (wf-prd w w₁ x₂ x₃)
  rewrite lem-iso-right x w | lem-iso-right x₁ w₁ = refl
lem-iso-right (an S (BSum x x₁)) (wf-sum w w₁ x₂ x₃)
  rewrite lem-iso-right x w | lem-iso-right x₁ w₁ = refl
lem-iso-right (an D x₁) w with lem-tToWft-dyn (wftTot (an D x₁) w D⊑D) 
lem-iso-right (an D x₁) w | proj₁ , proj₂ , proj₃ rewrite proj₃ = {!!}
\end{code}}
