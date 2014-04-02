module 2TT where

open import Level

{- I will be honest that I'm wondering if including the universe levels will actually be what I really /want/ to do, but on the other hand it seems like following Escardo et al.'s approach closely is probably the smartest thing I can do.

  Also, fundamentally, for the evaluation of things I don't know what I'll do. I might try to use that trick for making higher paths compute in Agda in order to get real equalities or maybe I'll just end up formalizing the canonicity proof from the paper. 
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
data TermTrans where

