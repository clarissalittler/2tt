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

data Subst where
  I : {i : Level} {Γ : Cxt i} -> Subst Γ Γ  
  _∘_ : {i j k : Level} {Γ : Cxt i} {Δ : Cxt j} {Ξ : Cxt k} -> Subst Δ Γ -> Subst Ξ Δ -> Subst Ξ Γ
  p : {i j : Level}{Γ : Cxt i}{A : Type j Γ} -> Subst (Γ · A) Γ
  {- this is different than the original theory because it's only projecting down one variable and not arbitrarily many at once, on the other hand that's okay because we can just repeat this operation repeatedly. -}
  ₍_,_₎ : {i j k : Level} {Γ : Cxt i} {Δ : Cxt j} {A : Type k Γ} (σ : Subst Δ Γ) -> Term Δ (A [ σ ]) -> Subst Δ (Γ · A)


{- so we also need the action of contexts transformations on substitutions -}

data CxtTrans where
  cRefl : {i j : Level} {Γ : Cxt i} {Δ : Cxt j} -> (θ : Subst Γ Δ) -> CxtTrans θ θ 
  cInv : {i j : Level} {Γ : Cxt i} {Δ : Cxt j} -> {θ θ' : Subst Γ Δ} -> CxtTrans θ θ' -> CxtTrans θ' θ
  cComp : {i j : Level} {Γ : Cxt i} {Δ : Cxt j} -> {θ θ' θ'' : Subst Γ Δ} -> CxtTrans θ' θ'' -> CxtTrans θ θ' -> CxtTrans θ θ''
  cResp : {i j k : Level} {Γ : Cxt i} {Δ : Cxt j} {Ω : Cxt k} -> {θ θ' : Subst Γ Δ} -> {ψ ψ' : Subst Ω Γ} -> CxtTrans θ θ' -> CxtTrans ψ ψ' -> CxtTrans (θ ∘ ψ) (θ' ∘ ψ')
{- need to add the cons case!! -}

data Term where  
  map : {i j k : Level} {Γ : Cxt i} {Δ : Cxt j} {θ θ' : Subst Γ Δ} {A : Type k Δ} -> (δ : CxtTrans θ θ') -> (M : Term Γ (A [ θ ])) -> Term Γ (A [ θ' ])
  _⟨_⟩ : {i j k : Level} {Γ : Cxt i} {Δ : Cxt j} {A : Type k Γ} -> Term Γ A -> (σ : Subst Δ Γ) -> Term Δ (A [ σ ])

data TermTrans where
  tRefl : {i j : Level} {Γ : Cxt i} {A : Type j Γ} -> (M : Term Γ A) -> TermTrans M M
  tInv : {i j : Level} {Γ : Cxt i} {A : Type j Γ} -> {M M' : Term Γ A} -> TermTrans M M' -> TermTrans M' M
  tComp : {i j : Level} {Γ : Cxt i} {A : Type j Γ} -> {M M' M'' : Term Γ A} -> TermTrans M' M'' -> TermTrans M M' -> TermTrans M M''
  tResp : {i j k : Level} {Γ : Cxt i} {Δ : Cxt j } {A : Type k Δ} {θ θ' : Subst Γ Δ} -> {M N : Term Δ A}
        -> (α : TermTrans M N) -> (δ : CxtTrans θ θ') -> TermTrans (map δ (M ⟨ θ ⟩ )) (N ⟨ θ' ⟩ )
