module 2TT where

open import Level

{- I will be honest that I'm wondering if including the universe levels will actually be what I really /want/ to do, but on the other hand it seems like following Escardo et al.'s approach closely is probably the smartest thing I can do.

  Also, fundamentally, for the evaluation of things I don't know what I'll do. I might try to use that trick for making higher paths compute in Agda in order to get real equalities or maybe I'll just end up formalizing the canonicity proof from the paper. 

  This also might all fail horribly but at least it'll be a cute exercise, doncha think?
  -}

data Cxt : Level -> Set
data Subst : {i j : Level} -> Cxt i -> Cxt j -> Set
data CxtTrans : {i j : Level} {c : Cxt i} {d : Cxt j} -> Subst c d -> Subst c d -> Set
data Type : {i : Level} -> Level -> Cxt i -> Set
data Term : {i j : Level} -> (Γ : Cxt i) -> Type j Γ -> Set
data TermTrans : {i j : Level} {Γ : Cxt i} {A : Type j Γ} -> Term Γ A -> Term Γ A -> Set

data Cxt where
  ε : {i : Level} -> Cxt i
  _·_ : {i j : Level} (Γ : Cxt i) -> Type j Γ -> Cxt (i ⊔ j)

data Type where
  _[_]  : {i j k : Level} {Γ : Cxt i} {Δ : Cxt j} → Type k Γ → Subst Δ Γ → Type k Δ
  Sigma : {i j k : Level} {Γ : Cxt i} (A : Type j Γ) -> Type k (Γ · A) -> Type (j ⊔ k) Γ
  Pi : {i j k : Level} {Γ : Cxt i} (A : Type j Γ) -> Type k (Γ · A) -> Type (j ⊔ k) Γ
  U : {i : Level} {Γ : Cxt i} (j : Level) -> Type (suc j) Γ
  El : {i j : Level} {Γ : Cxt i} -> Term Γ (U j) -> Type j Γ
  `2 : {i : Level} -> {Γ : Cxt i} -> Type i Γ
  Id : {i j : Level} {Γ : Cxt i} 
       -> (A : Type j Γ) 
       -> (M M' : Term Γ A) 
       -> Type j Γ

data Subst where
  I : {i : Level} {Γ : Cxt i} -> Subst Γ Γ  
  _∘_ : {i j k : Level} {Γ : Cxt i} {Δ : Cxt j} {Ξ : Cxt k} 
      -> Subst Δ Γ 
      -> Subst Ξ Δ 
      -> Subst Ξ Γ
  p : {i j : Level}{Γ : Cxt i}{A : Type j Γ} -> Subst (Γ · A) Γ
  {- this is different than the original theory because it's only projecting down one variable and not arbitrarily many at once, on the other hand that's okay because we can just repeat this operation repeatedly. -}
  ₍_,_₎ : {i j k : Level} {Γ : Cxt i} {Δ : Cxt j} {A : Type k Γ} 
          -> (σ : Subst Δ Γ) 
          -> Term Δ (A [ σ ]) 
          -> Subst Δ (Γ · A)

{- rar, okay, in addition to the pieces below as macros I think we also need a '''''''''macro''''''''' for map¹ -}

_⌜_⌝ : {i j k : Level} {Γ : Cxt i} {A : Type j Γ} → 
       Type k (Γ · A) 
       → Term Γ A 
       → Type k Γ

_⌞_⌟ : {i j k : Level} {Γ : Cxt i} {A : Type j Γ} {B : Type k (Γ · A)} 
       → Term (Γ · A) B 
       → (u : Term Γ A) 
       → Term Γ (B ⌜ u ⌝)

_⌈_⌉ : {i j k l : Level} {Γ : Cxt i} {Δ : Cxt j} {A : Type k Γ} →
       Type l (Γ · A) → 
       (σ : Subst Δ Γ) → 
       Type l (Δ · (A [ σ ]))

_⌊_⌋ : {i j k l : Level} {Γ : Cxt i} {Δ : Cxt j} {A : Type k Γ} {B : Type l (Γ · A)} 
       → Term (Γ · A) B 
       → (σ : Subst Δ Γ) 
       → Term (Δ · (A [ σ ])) (B ⌈ σ ⌉)

map¹ : {i j k : Level} {Γ : Cxt i} {A : Type j Γ} {B : Type k (Γ · A)} {N₁ N₂ : Term Γ A} 
          -> (α : TermTrans N₁ N₂) 
          -> (M : Term Γ (B ⌜ N₁ ⌝ )) 
          -> Term Γ (B ⌜ N₂ ⌝ ) 

data Term where  
  map : {i j k : Level} {Γ : Cxt i} {Δ : Cxt j} {θ θ' : Subst Γ Δ} {A : Type k Δ} 
           -> (δ : CxtTrans θ θ') 
           -> (M : Term Γ (A [ θ ])) 
           -> Term Γ (A [ θ' ])
  _⟨_⟩ : {i j k : Level} {Γ : Cxt i} {Δ : Cxt j} {A : Type k Δ} 
       -> Term Δ A 
       -> (σ : Subst Γ Δ) 
       -> Term Γ (A [ σ ])
  `λ : {i j k : Level} {Γ : Cxt i} {A : Type j Γ} {B : Type k (Γ · A)} 
       -> Term (Γ · A) B 
       -> Term Γ (Pi A B)
  App : {i j k : Level} {Γ : Cxt i} {A : Type j Γ} {B : Type k (Γ · A)} 
        -> Term Γ (Pi A B) 
        -> (M : Term Γ A) 
        -> Term Γ  (B ⌜ M ⌝)
  q : {i j : Level} {Γ : Cxt i} {A : Type j Γ} -> Term (Γ · A) (A [ p ]) -- 'sup bro, this is the projection from the last variable in the context...bro
  bool : {i j : Level} {Γ : Cxt i} -> Term Γ (U j)
  true : {i : Level} {Γ : Cxt i} -> Term Γ `2
  false : {i : Level} {Γ : Cxt i} -> Term Γ `2
  If : {i j : Level} {Γ : Cxt i} -> (M : Term Γ `2) -> (C : Type j (Γ · `2)) -> (N₁ : Term Γ (C ⌜ true ⌝)) -> (N₂ : Term Γ (C ⌜ false ⌝)) -> Term Γ (C ⌜ M ⌝)
  

data CxtTrans where
  cRefl : {i j : Level} {Γ : Cxt i} {Δ : Cxt j} 
          -> (θ : Subst Γ Δ) 
          -> CxtTrans θ θ 
  cInv : {i j : Level} {Γ : Cxt i} {Δ : Cxt j} -> {θ θ' : Subst Γ Δ} 
          -> CxtTrans θ θ' 
          -> CxtTrans θ' θ
  cComp : {i j : Level} {Γ : Cxt i} {Δ : Cxt j} -> {θ θ' θ'' : Subst Γ Δ} 
          -> CxtTrans θ' θ'' 
          -> CxtTrans θ θ' 
          -> CxtTrans θ θ''
  cResp : {i j k : Level} {Γ : Cxt i} {Δ : Cxt j} {Ω : Cxt k} -> {θ θ' : Subst Γ Δ} -> {ψ ψ' : Subst Ω Γ} 
          -> CxtTrans θ θ' 
          -> CxtTrans ψ ψ' 
          -> CxtTrans (θ ∘ ψ) (θ' ∘ ψ')
  csResp : {i j k : Level} {Γ : Cxt i} {Δ : Cxt j} {Ω : Cxt k} {ψ ψ' : Subst Ω Γ} 
           -> (θ : Subst Γ Δ) 
           -> (δ : CxtTrans ψ ψ') 
           -> CxtTrans (θ ∘ ψ ) (θ ∘ ψ' )
  ₍_,_₎ : {i j k : Level} {Γ : Cxt i} {Δ : Cxt j} {A : Type k Δ} {θ θ' : Subst Γ Δ} {M : Term Γ (A [ θ ])} {N : Term Γ (A [ θ' ])} 
             -> (δ : CxtTrans θ θ') 
             -> (α : TermTrans (map δ M) N) 
             -> CxtTrans ₍ θ , M ₎ ₍ θ' , N ₎ 

data TermTrans where
  tRefl : {i j : Level} {Γ : Cxt i} {A : Type j Γ} 
        -> (M : Term Γ A) 
        -> TermTrans M M
  tInv : {i j : Level} {Γ : Cxt i} {A : Type j Γ} -> {M M' : Term Γ A} 
         -> TermTrans M M' 
         -> TermTrans M' M
  tComp : {i j : Level} {Γ : Cxt i} {A : Type j Γ} -> {M M' M'' : Term Γ A} 
         -> TermTrans M' M'' 
         -> TermTrans M M' 
         -> TermTrans M M''
  tResp : {i j k : Level} {Γ : Cxt i} {Δ : Cxt j } {A : Type k Δ} {θ θ' : Subst Γ Δ} {M N : Term Δ A}
        -> (α : TermTrans M N) 
        -> (δ : CxtTrans θ θ') 
        -> TermTrans (map δ (M ⟨ θ ⟩ )) (N ⟨ θ' ⟩ )
  _[_] : {i j k : Level} {Γ : Cxt i} {Δ : Cxt j} {A : Type k Δ} {θ θ' : Subst Γ Δ} 
        -> (M : Term Δ A) 
        -> (δ : CxtTrans θ θ') 
        -> TermTrans (map δ (M ⟨ θ ⟩)) (M ⟨ θ' ⟩)
{-
  `λ : {i j k : Level} {Γ : Cxt i} {A : Type j Γ} {B : Type k (Γ · A)} {M N : Term Γ (Pi A B)} 
         -> (α : TermTrans (App (M ⟨ p ⟩ ) q) (App (N ⟨ p ⟩ ) q)) 
         -> TermTrans M N

-- this doesn't quite work off the bat, what do I actually need to put in here? SHOOT I'm not sure the rule as stated can actually be formalized because 
-- essentially they didn't include the weakenings in the right place, unless I figure out some general way to make a weakening for only the domain that's still a Π type. 
   I think to be completely formal we need to change this rule to something like...
-}

  `λ : {i j k : Level} {Γ : Cxt i} {A : Type j Γ} {B : Type k (Γ · A)} {M₁ M₂ : Term (Γ · A) B} 
         -> (α : TermTrans (App (`λ (M₁ ⟨ p ⟩)) q) (App (`λ (M₂ ⟨ p ⟩ )) q )) -> TermTrans (`λ M₁) (`λ M₂)
{- but shoot this means that we don't have general functional extensionality, right? Or can we derive it from the λ case? In seems like the general case should be a derived form by induction over the structure of terms, but that's not necessarily true eh? -}
  tApp : {i j k : Level} {Γ : Cxt i} {A : Type j Γ} {B : Type k (Γ · A)} {M₁ M₂ : Term Γ (Pi A B)} {N₁ N₂ : Term Γ A} 
         -> (α : TermTrans M₁ M₂) 
         -> (β : TermTrans N₁ N₂) 
         -> TermTrans (map¹ β (App M₁ N₁)) (App M₂ N₂)

B ⌜ u ⌝ = {!!}
u ⌞ v ⌟ = {!!} 
B ⌈ σ ⌉ = {!!} 
u ⌊ σ ⌋ = {!!}

map¹ = {!!}
