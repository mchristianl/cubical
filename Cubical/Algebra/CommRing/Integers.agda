{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.CommRing.Integers where

open import Cubical.Foundations.Prelude


open import Cubical.Algebra.CommRing

module _ where
  open import Cubical.HITs.Ints.BiInvInt
    renaming (
      _+_ to _+ℤ_;
      -_ to _-ℤ_;
      +-assoc to +ℤ-assoc;
      +-comm to +ℤ-comm
    )

  BiInvIntAsCommRing : CommRing {ℓ-zero}
  BiInvIntAsCommRing =
    makeCommRing
      zero (suc zero) _+ℤ_ _·_ _-ℤ_
      isSetBiInvInt
      +ℤ-assoc +-zero +-invʳ +ℤ-comm
      ·-assoc ·-identityʳ
      (λ x y z → sym (·-distribˡ x y z))
      ·-comm

-- makeCommRing ? ? ? ? ? ? ? ? ? ? ? ? ? ?

module _ where
  open import Cubical.Data.Int

  IntAsCommRing : CommRing {ℓ-zero}
  IntAsCommRing = makeCommRing {R = Int} 0 1 _+_ _·_ -_ isSetInt
    +-assoc +-identityʳ +-inverseʳ +-comm (λ x y z → sym (·-assoc x y z)) ·-identityʳ
    (λ x y z → sym (·-distribˡ x y z)) ·-comm

module _ where
  open import Cubical.HITs.Ints.QuoInt

  QuoIntAsCommRing : CommRing {ℓ-zero}
  QuoIntAsCommRing = makeCommRing {R = ℤ} 0 1 _+_ _·_ -_ isSetℤ
    +-assoc +-identityʳ +-inverseʳ +-comm ·-assoc ·-identityʳ
    (λ x y z → sym (·-distribˡ x y z)) ·-comm

module _ where
  open import Cubical.Data.DiffInt

  DiffIntAsCommRing : CommRing {ℓ-zero}
  DiffIntAsCommRing = makeCommRing {R = ℤ} 0 1 _+_ _·_ -_ isSetℤ
    +-assoc +-identityʳ +-inverseʳ +-comm ·-assoc ·-identityʳ ·-distribˡ ·-comm

open import Cubical.Algebra.Ring using (ringequiv)
open import Cubical.Foundations.Equiv
open import Cubical.Reflection.Base using (_$_) -- TODO: add this to Foundation.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Structure
open import Cubical.HITs.Ints.BiInvInt using (BiInvInt)
open import Cubical.Data.Nat using (suc; zero) renaming (_·_ to _·ⁿ_; _+_ to _+ⁿ_)
open import Cubical.Data.Int as Int using (sucInt; predInt; Int) renaming
  ( _+_ to _+'_
  ; _·_ to _·'_
  ; -_ to -'_
  ; pos to pos'
  ; negsuc to negsuc'
  ; sgn to sgn'
  ; abs to abs'
  ; signed to signed'
  )

module _ where
  open import Cubical.HITs.Ints.BiInvInt renaming
    ( fwd to ⟦_⟧
    ; suc to sucᵇ
    )

  private
    suc-⟦⟧ : ∀ x → sucᵇ ⟦ x ⟧ ≡ ⟦ sucInt x ⟧
    suc-⟦⟧ (pos' n) = refl
    suc-⟦⟧ (negsuc' zero) = suc-pred _
    suc-⟦⟧ (negsuc' (suc n)) = suc-pred _

    pred-⟦⟧ : ∀ x → predl ⟦ x ⟧ ≡ ⟦ predInt x ⟧
    pred-⟦⟧ (pos' zero) = refl
    pred-⟦⟧ (pos' (suc n)) = pred-suc _
    pred-⟦⟧ (negsuc' zero) = refl
    pred-⟦⟧ (negsuc' (suc n)) = refl

    neg-⟦⟧ : ∀ x → - ⟦ x ⟧ ≡ ⟦ -' x ⟧
    neg-⟦⟧ (pos' zero) = refl
    neg-⟦⟧ (pos' (suc n)) = (λ i → predl (neg-⟦⟧ (pos' n) i)) ∙ pred-⟦⟧ (-' pos' n) ∙ cong ⟦_⟧ (Int.predInt-neg (pos' n))
    neg-⟦⟧ (negsuc' zero) = refl
    neg-⟦⟧ (negsuc' (suc n)) = (λ i → sucᵇ (neg-⟦⟧ (negsuc' n) i))

    pres1 : 1 ≡ ⟦ 1 ⟧
    pres1 = refl

    isHom+ : ∀ x y → ⟦ x +' y ⟧ ≡ ⟦ x ⟧ + ⟦ y ⟧
    isHom+ (pos' zero) y i = ⟦ Int.+-comm 0 y i ⟧
    isHom+ (pos' (suc n)) y =
      ⟦ pos' (suc n) +' y ⟧     ≡[ i ]⟨ ⟦ Int.sucInt+ (pos' n) y (~ i) ⟧ ⟩
      ⟦ sucInt (pos' n +' y) ⟧  ≡⟨ sym $ suc-⟦⟧ _ ⟩
      sucᵇ  ⟦ pos' n +' y ⟧     ≡[ i ]⟨ sucᵇ $ isHom+ (pos' n) y i ⟩
      sucᵇ (⟦ pos' n ⟧ + ⟦ y ⟧) ≡⟨ refl ⟩
      sucᵇ  ⟦ pos' n ⟧ + ⟦ y ⟧  ∎
    isHom+ (negsuc' zero) y = pred-suc-inj _ _ (λ i → predl (γ i)) where
      -- γ =   sucᵇ ⟦  negsuc' zero +' y ⟧  ≡⟨ suc-⟦⟧ (negsuc' zero +' y) ⟩
      --     ⟦ sucInt (negsuc' zero +' y)⟧  ≡⟨ cong ⟦_⟧ $ Int.sucInt+ (negsuc' zero) y ∙ Int.+-comm 0 y ⟩
      --                       ⟦       y ⟧  ≡⟨ sym (suc-pred ⟦ y ⟧) ⟩
      --     sucᵇ (pred zero + ⟦       y ⟧) ∎
      γ = suc-⟦⟧ (negsuc' zero +' y) ∙ (λ i → ⟦ (Int.sucInt+ (negsuc' zero) y ∙ Int.+-comm 0 y) i ⟧) ∙ sym (suc-pred ⟦ y ⟧)
    isHom+ (negsuc' (suc n)) y = (λ i → ⟦ Int.predInt+ (negsuc' n) y (~ i) ⟧) ∙ sym (pred-⟦⟧ (negsuc' n +' y))
                               ∙ (λ i → pred $ isHom+ (negsuc' n) y i)

    isHom· : ∀ x y → ⟦ x ·' y ⟧ ≡ ⟦ x ⟧ · ⟦ y ⟧
    isHom· (pos' zero) y i = ⟦ Int.signed-zero (Int.sgn y) i ⟧
    isHom· (pos' (suc n)) y =
      ⟦ pos' (suc n) ·' y ⟧      ≡⟨ cong ⟦_⟧ $ Int.·-pos-suc n y ⟩
      ⟦ y +' pos' n ·' y ⟧       ≡⟨ isHom+ y _ ⟩
      ⟦ y ⟧ + ⟦ pos' n ·' y ⟧    ≡[ i ]⟨ ⟦ y ⟧ + isHom· (pos' n) y i ⟩
      ⟦ y ⟧ + ⟦ pos' n ⟧ · ⟦ y ⟧ ≡⟨ (λ i → ⟦ y ⟧ + ·-comm ⟦ pos' n ⟧ ⟦ y ⟧ i)
                                  ∙ sym (·-suc ⟦ y ⟧ ⟦ pos' n ⟧) ∙ ·-comm ⟦ y ⟧ _ ⟩
      sucᵇ ⟦ pos' n ⟧ · ⟦ y ⟧ ∎
    isHom· (negsuc' zero) y =
      ⟦ -1 ·'  y ⟧ ≡⟨ cong ⟦_⟧ (Int.·-neg1 y) ⟩
      ⟦ -'     y ⟧ ≡⟨ sym (neg-⟦⟧ y) ⟩
        -    ⟦ y ⟧ ≡⟨ sym (·-neg1 ⟦ y ⟧) ⟩
        -1 · ⟦ y ⟧ ∎
    isHom· (negsuc' (suc n)) y =
      ⟦ negsuc' (suc n) ·' y ⟧         ≡⟨ cong ⟦_⟧ $ Int.·-negsuc-suc n y ⟩
      ⟦ -' y   +'  negsuc' n   ·'  y ⟧ ≡⟨ isHom+ (-' y) _ ⟩
      ⟦ -' y ⟧ + ⟦ negsuc' n   ·'  y ⟧ ≡[ i ]⟨ ⟦ -' y ⟧ + isHom· (negsuc' n) y i ⟩
      ⟦ -' y ⟧ + ⟦ negsuc' n ⟧ · ⟦ y ⟧ ≡⟨ cong₂ _+_ (sym (neg-⟦⟧ y)) refl ⟩
      -  ⟦ y ⟧ + ⟦ negsuc' n ⟧ · ⟦ y ⟧ ≡⟨ (λ i → - ⟦ y ⟧ + ·-comm ⟦ negsuc' n ⟧ ⟦ y ⟧ i)
                                        ∙ sym (·-pred ⟦ y ⟧ ⟦ negsuc' n ⟧) ∙ ·-comm ⟦ y ⟧ _ ⟩
      pred ⟦ negsuc' n ⟧ · ⟦ y ⟧       ∎

    ⟦⟧-isEquiv : isEquiv ⟦_⟧
    ⟦⟧-isEquiv = isoToIsEquiv (iso ⟦_⟧ bwd fwd-bwd bwd-fwd)

  Int≃BiInvInt-CommRingEquivΣ : Σ[ e ∈ ⟨ IntAsCommRing ⟩ ≃ ⟨ BiInvIntAsCommRing ⟩ ] CommRingEquiv IntAsCommRing BiInvIntAsCommRing e
  Int≃BiInvInt-CommRingEquivΣ .fst = ⟦_⟧ , ⟦⟧-isEquiv
  Int≃BiInvInt-CommRingEquivΣ .snd = ringequiv pres1 isHom+ isHom·

  Int≡BiInvInt-AsCommRing : IntAsCommRing ≡ BiInvIntAsCommRing
  Int≡BiInvInt-AsCommRing = CommRingPath _ _ .fst Int≃BiInvInt-CommRingEquivΣ

module _ where
  open import Cubical.HITs.Ints.QuoInt as QuoInt renaming
    ( Int→ℤ to ⟦_⟧
    )
  open import Cubical.Data.Bool

  private
    suc-⟦⟧ : ∀ x → sucℤ ⟦ x ⟧ ≡ ⟦ sucInt x ⟧
    suc-⟦⟧ (pos' n) = refl
    suc-⟦⟧ (negsuc' zero) = sym posneg
    suc-⟦⟧ (negsuc' (suc n)) = refl

    pred-⟦⟧ : ∀ x → predℤ ⟦ x ⟧ ≡ ⟦ predInt x ⟧
    pred-⟦⟧ (pos' zero) = refl
    pred-⟦⟧ (pos' (suc n)) = refl
    pred-⟦⟧ (negsuc' n) = refl

    neg-⟦⟧ : ∀ x → - ⟦ x ⟧ ≡ ⟦ -' x ⟧
    neg-⟦⟧ (pos' zero) = sym posneg
    neg-⟦⟧ (pos' (suc n)) = refl
    neg-⟦⟧ (negsuc' n) = refl

    pres1 : 1 ≡ ⟦ 1 ⟧
    pres1 = refl

    isHom+ : ∀ x y → ⟦ x +' y ⟧ ≡ ⟦ x ⟧ + ⟦ y ⟧
    isHom+ (pos' zero) y i = ⟦ Int.+-comm 0 y i ⟧
    isHom+ (pos' (suc n)) y =
      ⟦ pos' (suc n)   +' y  ⟧ ≡[ i ]⟨ ⟦ Int.sucInt+ (pos' n) y (~ i) ⟧ ⟩
      ⟦ sucInt (pos' n +' y) ⟧ ≡⟨ sym $ suc-⟦⟧ _ ⟩
      sucℤ  ⟦ pos' n   +' y  ⟧ ≡[ i ]⟨ sucℤ $ isHom+ (pos' n) y i ⟩
      sucℤ (⟦ pos' n ⟧ + ⟦ y ⟧) ≡⟨ refl ⟩
      sucℤ  ⟦ pos' n ⟧ + ⟦ y ⟧  ∎
    isHom+ (negsuc'  zero  ) y = sucℤ-inj _ _ (suc-⟦⟧ (negsuc' zero +' y)
                               ∙ (cong ⟦_⟧ $ Int.sucInt+ (negsuc' zero) y
                               ∙ Int.+-identityˡ y)
                               ∙ sym (sucPredℤ ⟦ y ⟧))
    isHom+ (negsuc' (suc n)) y = cong ⟦_⟧ (sym (Int.predInt+ (negsuc' n) y))
                               ∙ (sym $ pred-⟦⟧ (negsuc' n +' y))
                               ∙ (λ i → predℤ $ isHom+ (negsuc' n) y i)

    isHom· : ∀ x y → ⟦ x ·' y ⟧ ≡ ⟦ x ⟧ · ⟦ y ⟧
    isHom· (pos' zero) y = (cong ⟦_⟧ $ Int.signed-zero (sgn' y)) ∙ sym (signed-zero (sign ⟦ y ⟧) spos)
    isHom· (pos' (suc n)) y =
      ⟦ pos' (suc n)     ·'  y ⟧ ≡⟨ cong ⟦_⟧ $ Int.·-pos-suc n y ⟩
      ⟦ y   +'  pos' n   ·'  y ⟧ ≡⟨ isHom+ y _ ⟩
      ⟦ y ⟧ + ⟦ pos' n   ·'  y ⟧ ≡[ i ]⟨ ⟦ y ⟧ + isHom· (pos' n) y i ⟩
      ⟦ y ⟧ + ⟦ pos' n ⟧ · ⟦ y ⟧ ≡⟨ sym $ ·-pos-suc n ⟦ y ⟧ ⟩
      sucℤ ⟦ pos' n ⟧ · ⟦ y ⟧ ∎
    isHom· (negsuc' zero) y =
      ⟦ -1 ·'  y ⟧ ≡⟨ cong ⟦_⟧ (Int.·-neg1 y) ⟩
      ⟦ -'     y ⟧ ≡⟨ sym (neg-⟦⟧ y) ⟩
        -    ⟦ y ⟧ ≡⟨ sym (·-neg1 ⟦ y ⟧) ⟩
        -1 · ⟦ y ⟧ ∎
    isHom· (negsuc' (suc n)) y =
      ⟦ negsuc' (suc n) ·' y ⟧         ≡⟨ cong ⟦_⟧ $ Int.·-negsuc-suc n y ⟩
      ⟦ -' y   +'  negsuc' n   ·'  y ⟧ ≡⟨ isHom+ (-' y) _ ⟩
      ⟦ -' y ⟧ + ⟦ negsuc' n   ·'  y ⟧ ≡[ i ]⟨ ⟦ -' y ⟧ + isHom· (negsuc' n) y i ⟩
      ⟦ -' y ⟧ + ⟦ negsuc' n ⟧ · ⟦ y ⟧ ≡⟨ cong₂ _+_ (sym (neg-⟦⟧ y)) refl ⟩
      -  ⟦ y ⟧ + ⟦ negsuc' n ⟧ · ⟦ y ⟧ ≡⟨ sym (·-neg-suc (suc n) ⟦ y ⟧) ⟩
      predℤ ⟦ negsuc' n ⟧ · ⟦ y ⟧      ∎

    ⟦⟧-isEquiv : isEquiv ⟦_⟧
    ⟦⟧-isEquiv = isoToIsEquiv (iso ⟦_⟧ ℤ→Int ℤ→Int→ℤ Int→ℤ→Int)

  Int≃QuoInt-CommRingEquivΣ : Σ[ e ∈ ⟨ IntAsCommRing ⟩ ≃ ⟨ QuoIntAsCommRing ⟩ ] CommRingEquiv IntAsCommRing QuoIntAsCommRing e
  Int≃QuoInt-CommRingEquivΣ .fst = ⟦_⟧ , ⟦⟧-isEquiv
  Int≃QuoInt-CommRingEquivΣ .snd = ringequiv pres1 isHom+ isHom·

  Int≡QuoInt-AsCommRing : IntAsCommRing ≡ QuoIntAsCommRing
  Int≡QuoInt-AsCommRing = CommRingPath _ _ .fst Int≃QuoInt-CommRingEquivΣ

QuoInt≡BiInvInt-AsCommRing : QuoIntAsCommRing ≡ BiInvIntAsCommRing
QuoInt≡BiInvInt-AsCommRing = sym Int≡QuoInt-AsCommRing ∙ Int≡BiInvInt-AsCommRing

open import Cubical.HITs.SetQuotients

module _ where
  open import Cubical.Data.Sigma
  open import Cubical.Data.Bool
  open import Cubical.Data.Nat using (ℕ) renaming (_·_ to _·ⁿ_)
  open import Cubical.HITs.Rationals.QuoQ using (ℚ) renaming (_+_ to _+ʳ_)
  open import Cubical.HITs.Ints.QuoInt using (ℤ; sign; signed; abs) renaming (_+_ to _+ᶻ_)
  open import Cubical.Data.NatPlusOne using (ℕ₊₁; 1+_)

  test1 : ℤ → _
  test1 x = {! x +ᶻ x  !}
  -- Normal form:
  --   x +ᶻ x

  test2 : ℤ × ℕ₊₁  → _
  test2 x = {! [ x ] +ʳ [ x ]  !}
  -- Normal form:
  --   [  signed (sign (fst x) ⊕ false) (abs (fst x) ·ⁿ suc (ℕ₊₁.n (snd x)))
  --   +ᶻ signed (sign (fst x) ⊕ false) (abs (fst x) ·ⁿ suc (ℕ₊₁.n (snd x)))
  --   , (1+ (ℕ₊₁.n (snd x) +ⁿ ℕ₊₁.n (snd x) ·ⁿ suc (ℕ₊₁.n (snd x))))
  --   ]

  test3 : ℚ → ℤ × ℕ₊₁  → _
  test3 x y = {! x +ʳ [ y ]  !}
  -- Normal form:
  --   rec
  --   (λ f g F G i j z →
  --      squash/ (f z) (g z) (λ i₁ → F i₁ z) (λ i₁ → G i₁ z) i j)
  --   (λ a → ...
  --     ...
  --   ... 2000 more lines ...

open import Cubical.Data.DiffInt as DiffInt hiding (_+'_; _·'_)

⟦⟧-isEquiv : isEquiv ⟦_⟧
⟦⟧-isEquiv = isoToIsEquiv (iso ⟦_⟧ bwd fwd-bwd bwd-fwd)

pres1 : 1 ≡ ⟦ 1 ⟧
pres1 = refl

isHom+ : ∀ x y → ⟦ x +' y ⟧ ≡ ⟦ x ⟧ + ⟦ y ⟧
isHom+ (pos' zero) y = {!   !}
isHom+ (pos' (suc n)) y = {!   !} -- ? ∙ λ i → sucℤ (isHom+ (pos' n) y i)
isHom+ (negsuc' zero) y = {! [ 0 , 1 ] + ⟦ y ⟧  !}
isHom+ (negsuc' (suc n)) y = {!   !}

isHom· : ∀ x y → ⟦ x ·' y ⟧ ≡ ⟦ x ⟧ · ⟦ y ⟧
isHom· = {!   !}

Int≃DiffInt-CommRingEquivΣ : Σ[ e ∈ ⟨ IntAsCommRing ⟩ ≃ ⟨ DiffIntAsCommRing ⟩ ] CommRingEquiv IntAsCommRing DiffIntAsCommRing e
Int≃DiffInt-CommRingEquivΣ .fst = ⟦_⟧ , ⟦⟧-isEquiv
Int≃DiffInt-CommRingEquivΣ .snd = ringequiv pres1 isHom+ isHom·

Int≡DiffInt-AsCommRing : IntAsCommRing ≡ DiffIntAsCommRing
Int≡DiffInt-AsCommRing = CommRingPath _ _ .fst Int≃DiffInt-CommRingEquivΣ

DiffInt≡BiInvInt-AsCommRing : DiffIntAsCommRing ≡ BiInvIntAsCommRing
DiffInt≡BiInvInt-AsCommRing = sym Int≡DiffInt-AsCommRing ∙ Int≡BiInvInt-AsCommRing
