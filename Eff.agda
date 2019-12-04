module Eff where

open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Function using (_∘_)
open import Data.Nat using (ℕ)
open import Data.List
open import Data.List.Properties
open import Relation.Binary.PropositionalEquality

postulate
  extensionality : ∀ {a b} → Extensionality a b

data Free (a : Set) : Set₁ where
  Return : a → Free a
  _>>=_  : ∀ {b} → Free b → (b → Free a) → Free a

St : Set
St = ℕ

data Req : Set → Set where
  Get  : Req St
  Put  : St → Req ⊤
  Zero : Req ⊥
  Coin : Req Bool

data isState : {a : Set} → Req a → Set where
  Get : isState Get
  Put : (s : St) → isState (Put s)

data isNondet : {a : Set} → Req a → Set where
  Zero : isNondet Zero
  Coin : isNondet Coin

data Eff (a : Set) : Set₁ where
  V : a → Eff a
  R : ∀ {b} → Req b → (b → Eff a) → Eff a

return : ∀ {a} → a → Eff a
return = V

_≈_ : {a b : Set} → Req a → Req b → Set
Get ≈ Get = ⊤
(Put _) ≈ (Put _) = ⊤
Zero ≈ Zero = ⊤
Coin ≈ Coin = ⊤
_ ≈ _ = ⊥

mutual

 ·⟫= : ∀ {a b} → (a → Eff b) → Eff a → Eff b
 ·⟫= f m = m ⟫= f

 {-# TERMINATING #-}
 _⟫=_ : ∀ {a b} → Eff a → (a → Eff b) → Eff b
 (V x)    ⟫= f = f x
 (R rq k) ⟫= f = R rq ((·⟫= f) ∘ k)

_⟫_ : ∀ {a b} → Eff a → Eff b → Eff b
m1 ⟫ m2 = m1 ⟫= (λ _ → m2)

liftM2 : ∀ {a} → (a → a → a) → Eff a → Eff a → Eff a
liftM2 op m1 m2 =
  m1 ⟫= λ x → m2 ⟫= λ y → return (op x y)

{-]
  Monad Laws:
     return x >>= f = f x
     m >>= return   = m
     (m >>= f) >>= g = m >>= λ x → f x >>= g
-}

monadLawRUnit : ∀ {a} (m : Eff a) → m ⟫= return ≡ m
monadLawRUnit (V x) = refl
monadLawRUnit (R rq k) = cong (R rq) (extensionality (λ x → monadLawRUnit (k x)))

monadLawAssoc : ∀ {a b c} →
   (m : Eff a) → (f : a → Eff b) → (g : b → Eff c) →
   (m ⟫= f) ⟫= g  ≡  m ⟫= λ x → f x ⟫= g
monadLawAssoc (V x) f g = refl
monadLawAssoc (R x k) f g = cong (R x) (extensionality (λ x₁ → monadLawAssoc (k x₁) _ _))

open ≡-Reasoning

liftM2Assoc : ∀ {a} (op : a → a → a)
  → (∀ (x y z : a) → op (op x y) z ≡ op x (op y z))
  → ∀ (m1 m2 m3 : Eff a)
  → liftM2 op (liftM2 op m1 m2) m3 ≡ liftM2 op m1 (liftM2 op m2 m3)
liftM2Assoc op pf m1 m2 m3 =
  begin
    liftM2 op (liftM2 op m1 m2) m3
  ≡⟨ refl ⟩
    ((m1 ⟫= λ x → m2 ⟫= λ y → return (op x y)) ⟫=
      λ x' → m3 ⟫= λ z → return (op x' z))
  ≡⟨ monadLawAssoc m1 _ _ ⟩
    (m1 ⟫= λ x → (m2 ⟫= λ y → return (op x y)) ⟫=
      λ x' → m3 ⟫= λ z → return (op x' z))
  ≡⟨ cong (λ f → m1 ⟫= f) (extensionality (λ x → monadLawAssoc m2 _ _)) ⟩
    (m1 ⟫= λ x → m2 ⟫= λ y → m3 ⟫= λ z → return (op (op x y) z))
  ≡⟨ cong (λ f → m1 ⟫= f)
      (extensionality (λ x → cong (λ f → m2 ⟫= f)
        (extensionality (λ y → cong ((λ f → m3 ⟫= f))
          (extensionality (λ z → cong V (pf _ _ _))))))) ⟩
    (m1 ⟫= λ x → m2 ⟫= λ y → m3 ⟫= λ z → return (op x (op y z)))
  ≡⟨ cong (λ f → m1 ⟫= f) (extensionality
      (λ x → cong (λ f → m2 ⟫= f)
        (extensionality (λ y → sym (monadLawAssoc m3 _ _))))) ⟩
    (m1 ⟫=
      λ x → (m2 ⟫= λ y → (m3 ⟫= λ z → return (op y z)) ⟫=
        λ y' → return (op x y')))
  ≡⟨ cong (λ f → m1 ⟫= f) (extensionality (λ x → sym (monadLawAssoc m2 _ _))) ⟩
    (m1 ⟫=
      λ x → (m2 ⟫= λ y → m3 ⟫= λ z → return (op y z)) ⟫=
        λ y' → return (op x y'))
  ≡⟨ refl ⟩
    liftM2 op m1 (liftM2 op m2 m3)
  ∎


--- State

hdState : ∀ {a} → St → Eff a → Eff (a × St)
hdState st (V x)           = V (x , st)
hdState st (R Get k)       = hdState st (k st)
hdState st (R (Put st') k) = hdState st' (k tt)
hdState st (R rq k)        = R rq (λ x → hdState st (k x))

get : Eff St
get = R Get return

put : St → Eff ⊤
put s = R (Put s) return

{- Basic state laws

    put s1 >> put s2  =  put s2
    put s >> get   = put s >> return s
    get >>= put = return ()
    get >>= λ s1 → get >>= λ s2 → f s1 s2 =
       get >>= λ s → f s s
-}

putPut : ∀ {s s1 s2} →
     hdState s (put s1 ⟫ put s2) ≡ hdState s (put s2)
putPut = refl

putGet : ∀ {s} → hdState s (put s ⟫ get) ≡ hdState s (put s ⟫ return s)
putGet = refl

getPut : ∀ {s} → hdState s (get ⟫= put) ≡ hdState s (return _)
getPut = refl

getGet : ∀ {a} {s} {f : St → St → Eff a}
  → hdState s (get ⟫= λ s₁ → get ⟫= λ s₂ → f s₁ s₂) ≡ hdState s (get ⟫= λ s → f s s)
getGet = refl

-- Non-Determinism
_++'_ : ∀ {a} → Eff (List a) → Eff (List a) → Eff (List a)
hm1 ++' hm2 = liftM2 (_++_) hm1 hm2

hdNondet : ∀ {a} → Eff a → Eff (List a)
hdNondet (V x)      = V (x ∷ [])
hdNondet (R Zero _) = V []
hdNondet (R Coin k) = (hdNondet (k true)) ++' (hdNondet (k false))
hdNondet (R rq k)   = R rq (λ x → hdNondet (k x))

_∥_ : ∀ {a} → Eff a → Eff a → Eff a
m1 ∥ m2 = R Coin (λ b → if b then m1 else m2)

∅ : ∀ {a} → Eff a
∅ = R Zero (λ ())
{- Basic laws about non-determinism monad

   m1 ∥ (m2 ∥ m3) = (m1 ∥ m2) ∥ m3
   m1 ∥ Zero = Zero = m1 ∥ Zero

   (m1 ∥ m2) >>= f = (m1 ⟫= f) ∥ (m2 ⟫= f)
-}

liftHdNondet : ∀ {a} → (m1 m2 : Eff a)
  → hdNondet (m1 ∥ m2) ≡ (hdNondet m1) ++' (hdNondet m2)
liftHdNondet m1 m2 = refl

liftHdNondetAssoc : ∀ {a} → (m1 m2 m3 : Eff a)
  → ((hdNondet m1 ++' hdNondet m2) ++' hdNondet m3) ≡ (hdNondet m1 ++' (hdNondet m2 ++' hdNondet m3))
liftHdNondetAssoc {a} m1 m2 m3 = liftM2Assoc _++_ ++-assoc (hdNondet m1) (hdNondet m2) (hdNondet m3)

hdNondetAssoc : ∀ {a} → (m1 m2 m3 : Eff a)
  → hdNondet ((m1 ∥ m2) ∥ m3) ≡ hdNondet (m1 ∥ (m2 ∥ m3))
hdNondetAssoc m1 m2 m3 = liftHdNondetAssoc m1 m2 m3

hdNondetZero : ∀ {a} → (k : a → Eff a) → hdNondet (∅ ⟫= k) ≡ hdNondet ∅
hdNondetZero k = refl

∥-distrib : ∀ {a} → (m1 m2 : Eff a) → (k : a → Eff a)
  → (m1 ∥ m2) ⟫= k ≡ R Coin (λ b → (if b then m1 else m2) ⟫= k)
∥-distrib m1 m2 k = refl

hdNondetDistrib : ∀ {a} → (m1 m2 : Eff a) → (k : a → Eff a)
  → hdNondet ((m1 ∥ m2) ⟫= k) ≡ hdNondet ((m1 ⟫= k) ∥ (m2 ⟫= k))
hdNondetDistrib m1 m2 k = refl

{- foldEff

-}

foldEff : ∀ {a : Set} {c : Set₁} → (a → c)
  → (∀ {b} → Req b → (b → c) → c)
  → Eff a
  → c
foldEff f g (V x) = f x
foldEff f g (R rq k) = g rq (foldEff f g ∘ k)

bindEqFold : ∀ {a b} → (f : a → Eff b) → (m : Eff a)
  → (m ⟫= f) ≡ foldEff f R m
bindEqFold f (V x) = refl
bindEqFold f (R rq k) = cong (R rq) (extensionality (λ x → bindEqFold f (k x)))

foldEff-∘ : ∀ {a b : Set} {c : Set₁} → (f₁ : b → c) → (f₂ : a → Eff b)
  → (g : ∀ {r} → Req r → (r → c) → c)
  → (m : Eff a)
  → ((foldEff f₁ g) ∘ (foldEff f₂ R)) m ≡ foldEff (foldEff f₁ g ∘ f₂) g m
foldEff-∘ f₁ f₂ g (V x) = refl
foldEff-∘ f₁ f₂ g (R rq k) =
  begin
    ((foldEff f₁ g) ∘ (foldEff f₂ R)) (R rq k)
  ≡⟨ refl ⟩
    foldEff f₁ g (R rq (foldEff f₂ R ∘ k))
  ≡⟨ refl ⟩
    g rq ((foldEff f₁ g ∘ foldEff f₂ R) ∘ k)
  ≡⟨ cong (g rq) (extensionality (λ x → foldEff-∘ f₁ f₂ g (k x))) ⟩
    g rq (foldEff (foldEff f₁ g ∘ f₂) g ∘ k)
  ≡⟨ refl ⟩
    foldEff (foldEff f₁ g ∘ f₂) g (R rq k)
  ∎
