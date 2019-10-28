module Eff where

open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Function using (_∘_)
open import Data.Nat using (ℕ)
open import Data.List
open import Relation.Binary.PropositionalEquality

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

data Eff (a : Set) : Set₁ where
  V : a → Eff a
  R : ∀ {b} → Req b → (b → Eff a) → Eff a

return : ∀ {a} → a → Eff a
return = V

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

{-
  Monad Laws:
     return x >>= f = f x
     m >>= return   = m
     (m >>= f) >>= g = m >>= λ x → f x >>= g
-}

monadLawRUnit : ∀ {a} (m : Eff a) → m ⟫= return ≡ m
monadLawRUnit (V x) = refl
monadLawRUnit (R rq k) = {!   !}

monadLawAssoc : ∀ {a b c} →
   (m : Eff a) → (f : a → Eff b) → (g : b → Eff c) →
   (m ⟫= f) ⟫= g  ≡  m ⟫= λ x → f x ⟫= g
monadLawAssoc (V x) f g = refl
monadLawAssoc (R x k) f g = {!    !}

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

--- getPut, and getGet

-- Non-Determinism

hdNondet : ∀ {a} → Eff a → Eff (List a)
hdNondet (V x)      = V (x ∷ [])
hdNondet (R Zero _) = V []
hdNondet (R Coin k) = liftM2 (_++_) (hdNondet (k false)) (hdNondet (k true))
hdNondet (R rq k)   = R rq (λ x → hdNondet (k x))

_∥_ : ∀ {a} → Eff a → Eff a → Eff a
m1 ∥ m2 = R Coin (λ b → if b then m1 else m2)

{- Basic laws about non-determinism monad

   m1 ∥ (m2 ∥ m3) = (m1 ∥ m2) ∥ m3
   m1 ∥ Zero = Zero = m1 ∥ Zero

   (m1 ∥ m2) >>= f = (m1 ⟫= f) ∥ (m2 ⟫= f)
-}
