{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Data.DiffInt.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.DiffInt.Base
open import Cubical.Data.Nat as ℕ using (suc; zero; isSetℕ; discreteℕ; ℕ) renaming (_+_ to _+ⁿ_; _·_ to _·ⁿ_)
open import Cubical.Data.Sigma
open import Cubical.Data.Int as Int using (Int; sucInt; predInt)
open import Cubical.Data.Bool

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary

open import Cubical.HITs.SetQuotients

open BinaryRelation

relIsEquiv : isEquivRel rel
relIsEquiv = equivRel {A = ℕ × ℕ} relIsRefl relIsSym relIsTrans
  where
    open import Cubical.Data.Nat

    relIsRefl : isRefl rel
    relIsRefl (a0 , a1) = refl

    relIsSym : isSym rel
    relIsSym (a0 , a1) (b0 , b1) p = sym p

    relIsTrans : isTrans rel
    relIsTrans (a0 , a1) (b0 , b1) (c0 , c1) p0 p1 =
      inj-m+ {m = (b0 + b1)} ((b0 + b1) + (a0 + c1) ≡⟨ +-assoc (b0 + b1) a0 c1  ⟩
            ((b0 + b1) + a0) + c1 ≡[ i ]⟨ +-comm b0 b1 i + a0   + c1 ⟩
            ((b1 + b0) + a0) + c1 ≡[ i ]⟨ +-comm (b1 + b0) a0 i + c1 ⟩
            (a0 + (b1 + b0)) + c1 ≡[ i ]⟨ +-assoc a0 b1 b0 i    + c1 ⟩
            (a0 + b1) + b0 + c1 ≡⟨ sym (+-assoc (a0 + b1) b0 c1) ⟩
            (a0 + b1) + (b0 + c1) ≡⟨ cong (λ p → p . fst + p .snd) (transport ΣPath≡PathΣ (p0 , p1))⟩
            (b0 + a1) + (c0 + b1) ≡⟨ sym (+-assoc b0 a1 (c0 + b1))⟩
            b0 + (a1 + (c0 + b1)) ≡[ i ]⟨ b0 + (a1 + +-comm c0 b1 i) ⟩
            b0 + (a1 + (b1 + c0)) ≡[ i ]⟨ b0 + +-comm a1 (b1 + c0) i ⟩
            b0 + ((b1 + c0) + a1) ≡[ i ]⟨ b0 + +-assoc b1 c0 a1 (~ i) ⟩
            b0 + (b1 + (c0 + a1)) ≡⟨ +-assoc b0 b1 (c0 + a1)⟩
            (b0 + b1) + (c0 + a1) ∎ )

relIsProp : BinaryRelation.isPropValued rel
relIsProp a b x y = isSetℕ _ _ _ _

discreteℤ : Discrete ℤ
discreteℤ = discreteSetQuotients (discreteΣ discreteℕ λ _ → discreteℕ) relIsProp relIsEquiv (λ _ _ → discreteℕ _ _)

private
  _ : Dec→Bool (discreteℤ [ (3 , 5) ] [ (4 , 6) ]) ≡ true
  _ = refl

  _ : Dec→Bool (discreteℤ [ (3 , 5) ] [ (4 , 7) ]) ≡ false
  _ = refl

isSetℤ : isSet ℤ
isSetℤ = Discrete→isSet discreteℤ

suc-identity : ∀ a⁺ a⁻ → [ suc a⁺ , suc a⁻ ] ≡ [ a⁺ , a⁻ ]
suc-identity a⁺ a⁻ = eq/ {R = rel} (suc a⁺ , suc a⁻) (a⁺ , a⁻) (sym (ℕ.+-suc _ _))

sucℤ' : ℕ × ℕ -> ℤ
sucℤ' (a⁺ , a⁻) = [ suc a⁺ , a⁻ ]

sucℤ'-respects-rel : (a b : ℕ × ℕ) → rel a b → sucℤ' a ≡ sucℤ' b
sucℤ'-respects-rel a@(a⁺ , a⁻) b@(b⁺ , b⁻) a~b = eq/ (suc a⁺ , a⁻) (suc b⁺ , b⁻) λ i → suc (a~b i)

sucℤ'' : ℤ -> ℤ
sucℤ'' = elim {R = rel} {B = λ _ → ℤ} (λ _ → isSetℤ) sucℤ' sucℤ'-respects-rel

-- normalization of isSetℤ explodes. Therefore we wrap this with expanded cases
sucℤ : ℤ -> ℤ
sucℤ x@([ _ ])             = sucℤ'' x
sucℤ x@(eq/ _ _ _ _)       = sucℤ'' x
sucℤ (squash/ a b p q i j) = isSetℤ _ _ (cong sucℤ p) (cong sucℤ q) i j

predℤ' : ℕ × ℕ -> ℤ
predℤ' (a⁺ , a⁻) = [ a⁺ , suc a⁻ ]

predℤ'-respects-rel : (a b : ℕ × ℕ) → rel a b → predℤ' a ≡ predℤ' b
predℤ'-respects-rel a@(a⁺ , a⁻) b@(b⁺ , b⁻) a~b =
  eq/ (a⁺ , suc a⁻) (b⁺ , suc b⁻) (ℕ.+-suc _ _ ∙∙ (λ i → suc (a~b i)) ∙∙ sym (ℕ.+-suc _ _))

predℤ'' : ℤ -> ℤ
predℤ'' = elim {R = rel} {B = λ _ → ℤ} (λ _ → isSetℤ) predℤ' predℤ'-respects-rel

-- normalization of isSetℤ explodes. Therefore we wrap this with expanded cases
predℤ : ℤ -> ℤ
predℤ x@([ _ ])             = predℤ'' x
predℤ x@(eq/ _ _ _ _)       = predℤ'' x
predℤ (squash/ a b p q i j) = isSetℤ _ _ (cong predℤ p) (cong predℤ q) i j

⟦_⟧ : Int -> ℤ
⟦_⟧ (Int.pos n) = [ n , 0 ]
⟦_⟧ (Int.negsuc n) = [ 0 , suc n ]

suc-⟦⟧ : ∀ x → sucℤ ⟦ x ⟧ ≡ ⟦ sucInt x ⟧
suc-⟦⟧ (Int.pos n) = refl
suc-⟦⟧ (Int.negsuc zero) = eq/ {R = rel} (1 , 1) (0 , 0) refl
suc-⟦⟧ (Int.negsuc (suc n)) = eq/ {R = rel} (1 , 2 +ⁿ n) (0 , 1 +ⁿ n) refl

pred-⟦⟧ : ∀ x → predℤ ⟦ x ⟧ ≡ ⟦ predInt x ⟧
pred-⟦⟧ (Int.pos zero) = refl
pred-⟦⟧ (Int.pos (suc n)) = eq/ (suc n , 1) (n , 0) (sym (ℕ.+-suc _ _))
pred-⟦⟧ (Int.negsuc n) = refl

fwd = ⟦_⟧

bwd' : ℕ × ℕ -> Int
bwd' (zero   , a⁻) = Int.neg a⁻
bwd' (suc a⁺ , a⁻) = sucInt (bwd' (a⁺ , a⁻))

rel-suc : ∀ a⁺ a⁻ → rel (a⁺ , a⁻) (suc a⁺ , suc a⁻)
rel-suc a⁺ a⁻ = ℕ.+-suc a⁺ a⁻

bwd'-suc : ∀ a⁺ a⁻ → bwd' (a⁺ , a⁻) ≡ bwd' (suc a⁺ , suc a⁻)
bwd'-suc zero zero = refl
bwd'-suc zero (suc a⁻) = refl
bwd'-suc (suc a⁺) a⁻ i = sucInt (bwd'-suc a⁺ a⁻ i)

bwd'+ : ∀ m n → bwd' (m , m +ⁿ n) ≡ bwd' (0 , n)
bwd'+ zero n = refl
bwd'+ (suc m) n = sym (bwd'-suc m (m +ⁿ n)) ∙ bwd'+ m n

bwd'-respects-rel : (a b : ℕ × ℕ) → rel a b → bwd' a ≡ bwd' b
bwd'-respects-rel (zero   , a⁻) (    b⁺ , b⁻) a~b = sym (bwd'+ b⁺ a⁻) ∙ (λ i → bwd' (b⁺ , a~b (~ i)))
bwd'-respects-rel (suc a⁺ , a⁻) (zero   , b⁻) a~b = (λ i → bwd' (suc a⁺ , a~b (~ i))) ∙ sym (bwd'-suc a⁺ (a⁺ +ⁿ b⁻)) ∙ bwd'+ a⁺ b⁻
bwd'-respects-rel (suc a⁺ , a⁻) (suc b⁺ , b⁻) a~b i = sucInt (bwd'-respects-rel (a⁺ , a⁻) (b⁺ , b⁻) (ℕ.inj-m+ {1} {a⁺ +ⁿ b⁻} {b⁺ +ⁿ a⁻} a~b) i)

bwd : ℤ -> Int
bwd = elim {R = rel} {B = λ _ → Int} (λ _ → Int.isSetInt) bwd' bwd'-respects-rel

bwd-fwd : ∀ (x : Int) -> bwd (fwd x) ≡ x
bwd-fwd (Int.pos zero) = refl
bwd-fwd (Int.pos (suc n)) i = sucInt (bwd-fwd (Int.pos n) i)
bwd-fwd (Int.negsuc n) = refl

fwd-bwd' : (a : ℕ × ℕ) → fwd (bwd [ a ]) ≡ [ a ]
fwd-bwd' a@(zero , zero) = refl
fwd-bwd' a@(zero , suc a⁻) = refl
fwd-bwd' a@(suc a⁺ , a⁻) = sym (suc-⟦⟧ (bwd [ a⁺ , a⁻ ])) ∙ (λ i → sucℤ (fwd-bwd' (a⁺ , a⁻) i))

fwd-bwd : ∀ (z : ℤ) -> fwd (bwd z) ≡ z
fwd-bwd = elimProp {R = rel} (λ _  → isSetℤ _ _) fwd-bwd'

Int≡ℤ : Int ≡ ℤ
Int≡ℤ = isoToPath (iso fwd bwd fwd-bwd bwd-fwd)

infix  8 -_
infixl 7 _·_
infixl 6 _+_

_+'_ : (a b : ℕ × ℕ) → ℤ
(a⁺ , a⁻) +' (b⁺ , b⁻) = [ a⁺ +ⁿ b⁺ , a⁻ +ⁿ b⁻ ]

private
  commˡⁿ : ∀ a b c → a +ⁿ b +ⁿ c ≡ a +ⁿ c +ⁿ b
  commˡⁿ a b c = sym (ℕ.+-assoc a b c) ∙ (λ i → a +ⁿ ℕ.+-comm b c i) ∙ ℕ.+-assoc a c b

  commʳⁿ : ∀ a b c → a +ⁿ (b +ⁿ c) ≡ b +ⁿ (a +ⁿ c)
  commʳⁿ a b c = (ℕ.+-assoc a b c) ∙ (λ i → ℕ.+-comm a b i +ⁿ c) ∙ sym (ℕ.+-assoc b a c)

  lem0 : ∀ a b c d → (a +ⁿ b) +ⁿ (c +ⁿ d) ≡ (a +ⁿ c) +ⁿ (b +ⁿ d)
  lem0 a b c d = ℕ.+-assoc (a +ⁿ b) c d ∙ (λ i → commˡⁿ a b c i +ⁿ d) ∙ sym (ℕ.+-assoc (a +ⁿ c) b d)

+ⁿ-creates-rel-≡ : ∀ a⁺ a⁻ x → _≡_ {A = ℤ} [ a⁺ , a⁻ ] [ a⁺ +ⁿ x , a⁻ +ⁿ x ]
+ⁿ-creates-rel-≡ a⁺ a⁻ x = eq/ (a⁺ , a⁻) (a⁺ +ⁿ x , a⁻ +ⁿ x) ((λ i → a⁺ +ⁿ ℕ.+-comm a⁻ x i) ∙ ℕ.+-assoc a⁺ x a⁻)

+-respects-relʳ : (a b c : ℕ × ℕ) → rel a b → (a +' c) ≡ (b +' c)
+-respects-relʳ a@(a⁺ , a⁻) b@(b⁺ , b⁻) c@(c⁺ , c⁻) p = eq/ {R = rel} (a⁺ +ⁿ c⁺ , a⁻ +ⁿ c⁻) (b⁺ +ⁿ c⁺ , b⁻ +ⁿ c⁻) (
  (a⁺ +ⁿ c⁺) +ⁿ (b⁻ +ⁿ c⁻) ≡⟨ lem0 a⁺ c⁺ b⁻ c⁻ ⟩
  (a⁺ +ⁿ b⁻) +ⁿ (c⁺ +ⁿ c⁻) ≡[ i ]⟨ p i +ⁿ (c⁺ +ⁿ c⁻) ⟩
  (b⁺ +ⁿ a⁻) +ⁿ (c⁺ +ⁿ c⁻) ≡⟨ sym (lem0 b⁺ c⁺ a⁻ c⁻) ⟩
  (b⁺ +ⁿ c⁺) +ⁿ (a⁻ +ⁿ c⁻) ∎)

+-respects-relˡ : (a b c : ℕ × ℕ) → rel b c → (a +' b) ≡ (a +' c)
+-respects-relˡ a@(a⁺ , a⁻) b@(b⁺ , b⁻) c@(c⁺ , c⁻) p = eq/ {R = rel} (a⁺ +ⁿ b⁺ , a⁻ +ⁿ b⁻) (a⁺ +ⁿ c⁺ , a⁻ +ⁿ c⁻) (
  (a⁺ +ⁿ b⁺) +ⁿ (a⁻ +ⁿ c⁻) ≡⟨ lem0 a⁺ b⁺ a⁻ c⁻ ⟩
  (a⁺ +ⁿ a⁻) +ⁿ (b⁺ +ⁿ c⁻) ≡[ i ]⟨ (a⁺ +ⁿ a⁻) +ⁿ p i ⟩
  (a⁺ +ⁿ a⁻) +ⁿ (c⁺ +ⁿ b⁻) ≡⟨ sym (lem0 a⁺ c⁺ a⁻ b⁻) ⟩
  (a⁺ +ⁿ c⁺) +ⁿ (a⁻ +ⁿ b⁻) ∎)

_+''_ : ℤ → ℤ → ℤ
_+''_ = rec2 {R = rel} {B = ℤ} φ _+'_ +-respects-relʳ +-respects-relˡ
  where abstract φ = isSetℤ

-- normalization of isSetℤ explodes. Therefore we wrap this with expanded cases
_+_ : ℤ → ℤ → ℤ
x@([ _ ])               + y@([ _ ])               = x +'' y
x@([ _ ])               + y@(eq/ _ _ _ _)         = x +'' y
x@(eq/ _ _ _ _)         + y@([ _ ])               = x +'' y
x@(eq/ _ _ _ _)         + y@(eq/ _ _ _ _)         = x +'' y
x@(eq/ _ _ _ _)         + y@(squash/ a b p q i j) = isSetℤ _ _ (cong (x +_) p) (cong (x +_) q) i j
x@([ _ ])               + y@(squash/ a b p q i j) = isSetℤ _ _ (cong (x +_) p) (cong (x +_) q) i j
x@(squash/ a b p q i j) + y                       = isSetℤ _ _ (cong (_+ y) p) (cong (_+ y) q) i j

-'_ : ℕ × ℕ → ℤ
-' (a⁺ , a⁻) = [ a⁻ , a⁺ ]

neg-respects-rel'-≡ : (a b : ℕ × ℕ) → rel a b → (-' a) ≡ (-' b)
neg-respects-rel'-≡ a@(a⁺ , a⁻) b@(b⁺ , b⁻) p = eq/ {R = rel} (a⁻ , a⁺) (b⁻ , b⁺) (ℕ.+-comm a⁻ b⁺ ∙ sym p ∙ ℕ.+-comm a⁺ b⁻)

-''_ : ℤ → ℤ
-''_ = rec {R = rel} {B = ℤ} isSetℤ -'_ neg-respects-rel'-≡

-- normalization of isSetℤ explodes. Therefore we wrap this with expanded cases
-_ : ℤ -> ℤ
- x@([ _ ])             = -'' x
- x@(eq/ _ _ _ _)       = -'' x
- (squash/ a b p q i j) = isSetℤ _ _ (cong -_ p) (cong -_ q) i j

neg-⟦⟧ : ∀ x → - ⟦ x ⟧ ≡ ⟦ Int.- x ⟧
neg-⟦⟧ (Int.pos zero) = refl
neg-⟦⟧ (Int.pos (suc n)) = refl
neg-⟦⟧ (Int.negsuc n) = refl

_·'_ : (a b : ℕ × ℕ) → ℤ
(a⁺ , a⁻) ·' (b⁺ , b⁻) = [ a⁺ ·ⁿ b⁺ +ⁿ a⁻ ·ⁿ b⁻ , a⁺ ·ⁿ b⁻ +ⁿ a⁻ ·ⁿ b⁺ ]

private
  lem1 : ∀ a b c d → (a +ⁿ b) +ⁿ (c +ⁿ d) ≡ (a +ⁿ d) +ⁿ (b +ⁿ c)
  lem1 a b c d = (λ i → (a +ⁿ b) +ⁿ ℕ.+-comm c d i) ∙ ℕ.+-assoc (a +ⁿ b) d c ∙ (λ i → commˡⁿ a b d i +ⁿ c) ∙ sym (ℕ.+-assoc (a +ⁿ d) b c)

·-respects-relʳ : (a b c : ℕ × ℕ) → rel a b → (a ·' c) ≡ (b ·' c)
·-respects-relʳ a@(a⁺ , a⁻) b@(b⁺ , b⁻) c@(c⁺ , c⁻) p = eq/ {R = rel} (a⁺ ·ⁿ c⁺ +ⁿ a⁻ ·ⁿ c⁻ , a⁺ ·ⁿ c⁻ +ⁿ a⁻ ·ⁿ c⁺) (b⁺ ·ⁿ c⁺ +ⁿ b⁻ ·ⁿ c⁻ , b⁺ ·ⁿ c⁻ +ⁿ b⁻ ·ⁿ c⁺) (
  (a⁺ ·ⁿ c⁺ +ⁿ a⁻ ·ⁿ c⁻) +ⁿ (b⁺ ·ⁿ c⁻ +ⁿ b⁻ ·ⁿ c⁺) ≡⟨ lem1 (a⁺ ·ⁿ c⁺) (a⁻ ·ⁿ c⁻) (b⁺ ·ⁿ c⁻) (b⁻ ·ⁿ c⁺) ⟩
  (a⁺ ·ⁿ c⁺ +ⁿ b⁻ ·ⁿ c⁺) +ⁿ (a⁻ ·ⁿ c⁻ +ⁿ b⁺ ·ⁿ c⁻) ≡[ i ]⟨ ℕ.·-distribʳ a⁺ b⁻ c⁺ i +ⁿ ℕ.·-distribʳ a⁻ b⁺ c⁻ i ⟩
  ((a⁺ +ⁿ b⁻) ·ⁿ c⁺) +ⁿ ((a⁻ +ⁿ b⁺) ·ⁿ c⁻)         ≡[ i ]⟨ p i ·ⁿ c⁺ +ⁿ (ℕ.+-comm a⁻ b⁺ ∙ sym p ∙ ℕ.+-comm a⁺ b⁻) i ·ⁿ c⁻ ⟩
  ((b⁺ +ⁿ a⁻) ·ⁿ c⁺) +ⁿ ((b⁻ +ⁿ a⁺) ·ⁿ c⁻)         ≡[ i ]⟨ ℕ.·-distribʳ b⁺ a⁻ c⁺ (~ i) +ⁿ ℕ.·-distribʳ b⁻ a⁺ c⁻ (~ i) ⟩
  (b⁺ ·ⁿ c⁺ +ⁿ a⁻ ·ⁿ c⁺) +ⁿ (b⁻ ·ⁿ c⁻ +ⁿ a⁺ ·ⁿ c⁻) ≡⟨ sym (lem1 (b⁺ ·ⁿ c⁺) (b⁻ ·ⁿ c⁻) (a⁺ ·ⁿ c⁻) (a⁻ ·ⁿ c⁺)) ⟩
  (b⁺ ·ⁿ c⁺ +ⁿ b⁻ ·ⁿ c⁻) +ⁿ (a⁺ ·ⁿ c⁻ +ⁿ a⁻ ·ⁿ c⁺) ∎)

·-respects-relˡ : (a b c : ℕ × ℕ) → rel b c → (a ·' b) ≡ (a ·' c)
·-respects-relˡ a@(a⁺ , a⁻) b@(b⁺ , b⁻) c@(c⁺ , c⁻) p = eq/ {R = rel} (a⁺ ·ⁿ b⁺ +ⁿ a⁻ ·ⁿ b⁻ , a⁺ ·ⁿ b⁻ +ⁿ a⁻ ·ⁿ b⁺) (a⁺ ·ⁿ c⁺ +ⁿ a⁻ ·ⁿ c⁻ , a⁺ ·ⁿ c⁻ +ⁿ a⁻ ·ⁿ c⁺) (
  (a⁺ ·ⁿ b⁺ +ⁿ a⁻ ·ⁿ b⁻) +ⁿ (a⁺ ·ⁿ c⁻ +ⁿ a⁻ ·ⁿ c⁺) ≡⟨ lem0 (a⁺ ·ⁿ b⁺) (a⁻ ·ⁿ b⁻) (a⁺ ·ⁿ c⁻) (a⁻ ·ⁿ c⁺) ⟩
  (a⁺ ·ⁿ b⁺ +ⁿ a⁺ ·ⁿ c⁻) +ⁿ (a⁻ ·ⁿ b⁻ +ⁿ a⁻ ·ⁿ c⁺) ≡[ i ]⟨ ℕ.·-distribˡ a⁺ b⁺ c⁻ i +ⁿ ℕ.·-distribˡ a⁻ b⁻ c⁺ i ⟩
  (a⁺ ·ⁿ (b⁺ +ⁿ c⁻)) +ⁿ (a⁻ ·ⁿ (b⁻ +ⁿ c⁺))         ≡[ i ]⟨ a⁺ ·ⁿ p i +ⁿ a⁻ ·ⁿ (ℕ.+-comm b⁻ c⁺ ∙ sym p ∙ ℕ.+-comm b⁺ c⁻) i ⟩
  (a⁺ ·ⁿ (c⁺ +ⁿ b⁻)) +ⁿ (a⁻ ·ⁿ (c⁻ +ⁿ b⁺))         ≡[ i ]⟨ ℕ.·-distribˡ a⁺ c⁺ b⁻ (~ i) +ⁿ ℕ.·-distribˡ a⁻ c⁻ b⁺ (~ i) ⟩
  (a⁺ ·ⁿ c⁺ +ⁿ a⁺ ·ⁿ b⁻) +ⁿ (a⁻ ·ⁿ c⁻ +ⁿ a⁻ ·ⁿ b⁺) ≡⟨ sym (lem0 (a⁺ ·ⁿ c⁺) (a⁻ ·ⁿ c⁻) (a⁺ ·ⁿ b⁻) (a⁻ ·ⁿ b⁺)) ⟩
  (a⁺ ·ⁿ c⁺ +ⁿ a⁻ ·ⁿ c⁻) +ⁿ (a⁺ ·ⁿ b⁻ +ⁿ a⁻ ·ⁿ b⁺) ∎)

_·''_ : ℤ → ℤ → ℤ
_·''_ = rec2 {R = rel} {B = ℤ} isSetℤ _·'_ ·-respects-relʳ ·-respects-relˡ

-- normalization of isSetℤ explodes. Therefore we wrap this with expanded cases
_·_ : ℤ → ℤ → ℤ
x@([ _ ])               · y@([ _ ])               = x ·'' y
x@([ _ ])               · y@(eq/ _ _ _ _)         = x ·'' y
x@(eq/ _ _ _ _)         · y@([ _ ])               = x ·'' y
x@(eq/ _ _ _ _)         · y@(eq/ _ _ _ _)         = x ·'' y
x@(eq/ _ _ _ _)         · y@(squash/ a b p q i j) = isSetℤ _ _ (cong (x ·_) p) (cong (x ·_) q) i j
x@([ _ ])               · y@(squash/ a b p q i j) = isSetℤ _ _ (cong (x ·_) p) (cong (x ·_) q) i j
x@(squash/ a b p q i j) · y                       = isSetℤ _ _ (cong (_· y) p) (cong (_· y) q) i j

+-identityˡ : (x : ℤ) → 0 + x ≡ x
+-identityˡ = elimProp {R = rel} (λ _ → isSetℤ _ _) λ _ → refl

+sucℤ : ∀ x y → sucℤ (x + y) ≡ sucℤ x + y
+sucℤ = elimProp2 {R = rel} (λ _ _ → isSetℤ _ _) (λ _ _ → refl)

+predℤ : ∀ x y → predℤ (x + y) ≡ predℤ x + y
+predℤ = elimProp2 {R = rel} (λ _ _ → isSetℤ _ _) (λ _ _ → refl)

sucℤ-inj : ∀ x y → sucℤ x ≡ sucℤ y → x ≡ y
sucℤ-inj = elimProp2 {R = rel} (λ _ _ → isPropΠ (λ _ → (isSetℤ _ _)))
  λ{ (a⁺ , a⁻) (b⁺ , b⁻) p → sym (suc-identity a⁺ a⁻) ∙ cong predℤ p ∙ suc-identity b⁺ b⁻ }

·-nullifiesˡ : ∀ x → 0 · x ≡ 0
·-nullifiesˡ = elimProp {R = rel} (λ _ → isSetℤ _ _) λ _ → refl

·-pos-suc : ∀ x y → sucℤ x · y ≡ y + x · y
·-pos-suc = elimProp2 {R = rel} (λ _ _ → isSetℤ _ _)
  λ{ (a⁺ , a⁻) (b⁺ , b⁻) i → [ ℕ.+-assoc b⁺ (a⁺ ·ⁿ b⁺) (a⁻ ·ⁿ b⁻) (~ i) , ℕ.+-assoc b⁻ (a⁺ ·ⁿ b⁻) (a⁻ ·ⁿ b⁺) (~ i) ] }

·-neg1 : ∀ x → -1 · x ≡ - x
·-neg1 = elimProp {R = rel} (λ _ → isSetℤ _ _)
  λ{ (a⁺ , a⁻) i → [ ℕ.+-zero a⁻ i , ℕ.+-zero a⁺ i ] }

·-neg-suc : ∀ x y → predℤ x · y ≡ - y + x · y
·-neg-suc = elimProp2 {R = rel} (λ _ _ → isSetℤ _ _)
  λ{ (a⁺ , a⁻) (b⁺ , b⁻) i → [ commʳⁿ (a⁺ ·ⁿ b⁺) b⁻ (a⁻ ·ⁿ b⁻) i , commʳⁿ (a⁺ ·ⁿ b⁻) b⁺ (a⁻ ·ⁿ b⁺) i ] }

-- +-identityʳ : (x : ℤ) → x + 0 ≡ x
-- +-identityʳ = elimProp {R = rel} (λ _ → isSetℤ _ _)
--   λ{ (a⁺ , a⁻) i → [ ℕ.+-comm a⁺ 0 i , ℕ.+-comm a⁻ 0 i ] }
--
-- +-comm : (x y : ℤ) → x + y ≡ y + x
-- +-comm = elimProp2 {R = rel} (λ _ _ → isSetℤ _ _)
--   λ{ (a⁺ , a⁻) (b⁺ , b⁻) i → [ ℕ.+-comm a⁺ b⁺ i , ℕ.+-comm a⁻ b⁻ i ] }
