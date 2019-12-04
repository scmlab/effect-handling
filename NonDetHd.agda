module NonDetHd where

open import Eff
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Function using (_∘_)
open ≡-Reasoning


data NonDetOnly {a : Set} :  Eff a → Set₁ where
  V : ∀ (x : a) → NonDetOnly (V x)
  R : ∀ {b r : Set}
    → (rq : Req r) → (k : r → Eff a)
    → ((rq ≈ Coin) ⊎ (rq ≈ Zero))
    → (∀ y → NonDetOnly (k y))
    → NonDetOnly (R rq k)

postulate
  a b : Set
  hd : Eff a → Eff b
  hdR : ∀ {r : Set}
    → (rq : Req r) → (k : r → Eff a)
    → ((rq ≈ Coin) ⊎ (rq ≈ Zero))
    → hd (R rq k) ≡ R rq (hd ∘ k)

hdEqFold : (m : Eff a)
  → NonDetOnly m
  → hd m ≡ foldEff (λ x → hd (V x)) R m
hdEqFold (V x) p = refl
hdEqFold (R rq k) (R rq k p1 p2) =
  begin
    hd (R rq k)
  ≡⟨ hdR rq k p1 ⟩
    R rq (hd ∘ k)
  ≡⟨ cong (R rq) (extensionality (λ x → hdEqFold (k x) (p2 x))) ⟩
    foldEff (λ x → hd (V x)) R (R rq k)
  ∎

hdBind : {c : Set} (m : Eff c)
  → (f : c → Eff a)
  → NonDetOnly m
  → hd (m ⟫= f) ≡ foldEff (hd ∘ f) R m
hdBind (V x) f p = refl
hdBind (R rq k) f (R rq k p1 p2) =
  begin
    hd (R rq k ⟫= f)
  ≡⟨ hdR rq (λ x → ·⟫= f (k x)) p1 ⟩
    R rq (hd ∘ (·⟫= f ∘ k))
  ≡⟨ cong (R rq) (extensionality (λ x → hdBind (k x) f (p2 x))) ⟩
    foldEff (hd ∘ f) R (R rq k)
  ∎

hdExt : {c : Set} (m : Eff c)
  → (f1 f2 : c → Eff a)
  → NonDetOnly m
  → hd ∘ f1 ≡ hd ∘ f2
  → hd (m ⟫= f1) ≡ hd (m ⟫= f2)
hdExt m f1 f2 pm pf =
  begin
    hd (m ⟫= f1)
  ≡⟨ hdBind m f1 pm ⟩
    foldEff (hd ∘ f1) R m
  ≡⟨ cong-app (cong₂ foldEff pf refl) m ⟩
    foldEff (hd ∘ f2) R m
  ≡⟨ sym (hdBind m f2 pm) ⟩
    hd (m ⟫= f2)
  ∎

-- hdApplyEq : (m1 m2 : Eff a)
--   → (f : a → Eff a)
--   → NonDetOnly m1 → NonDetOnly m2
--   → (∀ (x y) → hd (V x) ≡ hd (V y) → hd (f x) ≡ hd (f y))
--   → hd m1 ≡ hd m2
--   → hd (m1 ⟫= f) ≡ hd (m2 ⟫= f)
-- hdApplyEq m1 m2 f pm1 pm2 p1 p2 =
--   begin
--     hd (m1 ⟫= f)
--   ≡⟨ hdBind m1 f pm1 ⟩
--     foldEff (hd ∘ f) R m1
--   ≡⟨ {!   !} ⟩
--     foldEff (hd ∘ f) R m2
--   ≡⟨ sym (hdBind m2 f pm2) ⟩
--     hd (m2 ⟫= f)
--   ∎
-- trans (sym (hdEqFold m1 pm1)) (hdEqFold m2 pm2)

open import Data.List
open import Data.List.Properties

hdZero : hdNondet (hd ∅) ≡ V []
hdZero = cong hdNondet (hdR Zero (λ ()) (inj₂ tt))

hdCoin : ∀ (m1 m2 : Eff a)
  → hdNondet (hd (m1 ∥ m2)) ≡ hdNondet (hd m1) ++' hdNondet (hd m2)
hdCoin m1 m2 = cong hdNondet (hdR Coin (λ b₁ → if b₁ then m1 else m2) (inj₁ tt))

hdAssoc : ∀ (m1 m2 m3 : Eff a)
  → hdNondet (hd ((m1 ∥ m2) ∥ m3)) ≡ hdNondet (hd (m1 ∥ (m2 ∥ m3)))
hdAssoc m1 m2 m3 =
  begin
    hdNondet (hd ((m1 ∥ m2) ∥ m3))
  ≡⟨ hdCoin (m1 ∥ m2) m3 ⟩
    hdNondet (hd (m1 ∥ m2)) ++' hdNondet (hd m3)
  ≡⟨ cong (λ x → x ++' hdNondet (hd m3)) (hdCoin m1 m2) ⟩
    (hdNondet (hd m1) ++' hdNondet (hd m2)) ++' hdNondet (hd m3)
  ≡⟨ liftM2Assoc _++_ ++-assoc (hdNondet (hd m1)) (hdNondet (hd m2)) (hdNondet (hd m3)) ⟩
    hdNondet (hd m1) ++' (hdNondet (hd m2) ++' hdNondet (hd m3))
  ≡⟨ sym (cong (λ x → hdNondet (hd m1) ++' x) (hdCoin m2 m3)) ⟩
    hdNondet (hd m1) ++' (hdNondet (hd (m2 ∥ m3)))
  ≡⟨ sym (hdCoin m1 (m2 ∥ m3)) ⟩
    hdNondet (hd (m1 ∥ (m2 ∥ m3)))
  ∎

hdLeftZero : ∀ {c : Set} (k : c → Eff a)
  → hdNondet (hd (∅ ⟫= k)) ≡ hdNondet (hd ∅)
hdLeftZero k = trans (trans (cong hdNondet (hdR Zero _ (inj₂ tt))) refl) (sym hdZero)
