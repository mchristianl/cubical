{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.CommRing.Integers where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Reflection.Base using (_$_) -- TODO: add this to Foundation.Function

open import Cubical.Data.Nat using (suc; zero)
import Cubical.Data.Int as Int
module Int' = Int using (sucInt; predInt; Int) renaming
  ( _+_    to _+'_
  ; _·_    to _·'_
  ; -_     to -'_
  ; pos    to pos'
  ; negsuc to negsuc'
  ; sgn    to sgn'
  )

open import Cubical.Structures.Axioms using (transferAxioms)
open import Cubical.Algebra.Ring as RRing using (ringequiv; RingEquiv)
open import Cubical.Algebra.CommRing

open RRing.RingΣTheory using (RawRingStructure; RawRingEquivStr; rawRingUnivalentStr)
open Cubical.Algebra.CommRing.CommRingΣTheory using (CommRingAxioms; CommRingStructure; CommRing→CommRingΣ; CommRingΣ→CommRing)

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

  BiInvIntΣraw : TypeWithStr ℓ-zero RawRingStructure
  BiInvIntΣraw = BiInvInt , _+ℤ_ , 1 , _·_

module _ where
  open Int'
  open import Cubical.HITs.Ints.BiInvInt renaming ( fwd to ⟦_⟧ ; suc to sucᵇ)

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
      γ : sucᵇ (⟦ negsuc' zero +' y ⟧) ≡ sucᵇ (pred zero + ⟦ y ⟧)
      γ = suc-⟦⟧ (negsuc' zero +' y) ∙ (λ i → ⟦ (Int.sucInt+ (negsuc' zero) y ∙ Int.+-comm 0 y) i ⟧) ∙ sym (suc-pred ⟦ y ⟧)
    isHom+ (negsuc' (suc n)) y = (λ i → ⟦ Int.predInt+ (negsuc' n) y (~ i) ⟧) ∙ sym (pred-⟦⟧ (negsuc' n +' y)) ∙ (λ i → pred $ isHom+ (negsuc' n) y i)

    isHom· : ∀ x y → ⟦ x ·' y ⟧ ≡ ⟦ x ⟧ · ⟦ y ⟧
    isHom· (pos' zero) y i = ⟦ Int.signed-zero (Int.sgn y) i ⟧
    isHom· (pos' (suc n)) y =
      ⟦ pos' (suc n) ·' y ⟧      ≡⟨ cong ⟦_⟧ $ Int.·-pos-suc n y ⟩
      ⟦ y +' pos' n ·' y ⟧       ≡⟨ isHom+ y _ ⟩
      ⟦ y ⟧ + ⟦ pos' n ·' y ⟧    ≡[ i ]⟨ ⟦ y ⟧ + isHom· (pos' n) y i ⟩
      ⟦ y ⟧ + ⟦ pos' n ⟧ · ⟦ y ⟧ ≡⟨ (λ i → ⟦ y ⟧ + ·-comm ⟦ pos' n ⟧ ⟦ y ⟧ i) ∙ sym (·-suc ⟦ y ⟧ ⟦ pos' n ⟧) ∙ ·-comm ⟦ y ⟧ _ ⟩
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
      -  ⟦ y ⟧ + ⟦ negsuc' n ⟧ · ⟦ y ⟧ ≡⟨ (λ i → - ⟦ y ⟧ + ·-comm ⟦ negsuc' n ⟧ ⟦ y ⟧ i) ∙ sym (·-pred ⟦ y ⟧ ⟦ negsuc' n ⟧) ∙ ·-comm ⟦ y ⟧ _ ⟩
      pred ⟦ negsuc' n ⟧ · ⟦ y ⟧       ∎

    ⟦⟧-isEquiv : isEquiv ⟦_⟧
    ⟦⟧-isEquiv = isoToIsEquiv (iso ⟦_⟧ bwd fwd-bwd bwd-fwd)

  IntΣraw : TypeWithStr ℓ-zero RawRingStructure
  IntΣraw = Int , _+'_ , 1 , _·'_

  BiInvInt≃Int-Σraw : BiInvIntΣraw ≃[ RawRingEquivStr ] IntΣraw
  BiInvInt≃Int-Σraw = ≃[]-swap rawRingUnivalentStr IntΣraw BiInvIntΣraw ((_ , ⟦⟧-isEquiv) , (isHom+ , pres1 , isHom·))

  Int-CommRingAxioms : CommRingAxioms Int (str IntΣraw)
  Int-CommRingAxioms = transferAxioms {S = RawRingStructure} rawRingUnivalentStr {axioms = CommRingAxioms} (CommRing→CommRingΣ BiInvIntAsCommRing) IntΣraw BiInvInt≃Int-Σraw

  IntΣ : TypeWithStr _ CommRingStructure
  IntΣ = (typ IntΣraw) , (str IntΣraw) , Int-CommRingAxioms

  IntAsCommRing : CommRing
  IntAsCommRing = CommRingΣ→CommRing IntΣ

  Int≃BiInvInt-CommRingEquiv : Σ[ e ∈ ⟨ IntAsCommRing ⟩ ≃ ⟨ BiInvIntAsCommRing ⟩ ] CommRingEquiv IntAsCommRing BiInvIntAsCommRing e
  Int≃BiInvInt-CommRingEquiv .fst = _ , ⟦⟧-isEquiv
  Int≃BiInvInt-CommRingEquiv .snd = ringequiv pres1 isHom+ isHom·

  Int≡BiInvInt-AsCommRing : IntAsCommRing ≡ BiInvIntAsCommRing
  Int≡BiInvInt-AsCommRing = CommRingPath _ _ .fst Int≃BiInvInt-CommRingEquiv

module _ where
  open Int'
  open import Cubical.HITs.Ints.QuoInt as QuoInt renaming ( Int→ℤ to ⟦_⟧ ; ℤ to QuoInt )
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
    isHom+ (negsuc'  zero  ) y = sucℤ-inj _ _
                                 ( suc-⟦⟧ (negsuc' zero +' y)
                                 ∙ (cong ⟦_⟧ $ Int.sucInt+ (negsuc' zero) y ∙ Int.+-identityˡ y)
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

  QuoIntΣraw : TypeWithStr ℓ-zero RawRingStructure
  QuoIntΣraw = QuoInt , _+_ , 1 , _·_

  Int≃QuoInt-Σraw : IntΣraw ≃[ RawRingEquivStr ] QuoIntΣraw
  Int≃QuoInt-Σraw = ((_ , ⟦⟧-isEquiv) , (isHom+ , pres1 , isHom·))

  QuoInt-CommRingAxioms : CommRingAxioms QuoInt (str QuoIntΣraw)
  QuoInt-CommRingAxioms = transferAxioms {S = RawRingStructure} rawRingUnivalentStr {axioms = CommRingAxioms} (CommRing→CommRingΣ IntAsCommRing) QuoIntΣraw Int≃QuoInt-Σraw

  QuoIntΣ : TypeWithStr _ CommRingStructure
  QuoIntΣ = (typ QuoIntΣraw) , (str QuoIntΣraw) , QuoInt-CommRingAxioms

  QuoIntAsCommRing : CommRing
  QuoIntAsCommRing = CommRingΣ→CommRing QuoIntΣ

  Int≃QuoInt-CommRingEquiv : Σ[ e ∈ ⟨ IntAsCommRing ⟩ ≃ ⟨ QuoIntAsCommRing ⟩ ] CommRingEquiv IntAsCommRing QuoIntAsCommRing e
  Int≃QuoInt-CommRingEquiv .fst = _ , ⟦⟧-isEquiv
  Int≃QuoInt-CommRingEquiv .snd = ringequiv pres1 isHom+ isHom·

  Int≡QuoInt-AsCommRing : IntAsCommRing ≡ QuoIntAsCommRing
  Int≡QuoInt-AsCommRing = CommRingPath _ _ .fst Int≃QuoInt-CommRingEquiv

QuoInt≡BiInvInt-AsCommRing : QuoIntAsCommRing ≡ BiInvIntAsCommRing
QuoInt≡BiInvInt-AsCommRing = sym Int≡QuoInt-AsCommRing ∙ Int≡BiInvInt-AsCommRing

module _ where
  open Int'
  open import Cubical.Data.DiffInt as DiffInt hiding (_+'_; _·'_; -'_) renaming (ℤ to DiffInt)
  open import Cubical.HITs.SetQuotients

  private
    ⟦⟧-isEquiv : isEquiv ⟦_⟧
    ⟦⟧-isEquiv = isoToIsEquiv (iso ⟦_⟧ bwd fwd-bwd bwd-fwd)

    pres1 : 1 ≡ ⟦ 1 ⟧
    pres1 = refl

    isHom+ : ∀ x y → ⟦ x +' y ⟧ ≡ ⟦ x ⟧ + ⟦ y ⟧
    isHom+ (pos' zero) y = (λ i → ⟦ Int.+-comm 0 y i ⟧) ∙ sym (+-identityˡ ⟦ y ⟧)
    isHom+ (pos' (suc n)) y =
      ⟦ pos' (suc n)   +' y  ⟧  ≡[ i ]⟨ ⟦ Int.sucInt+ (pos' n) y (~ i) ⟧ ⟩
      ⟦ sucInt (pos' n +' y) ⟧  ≡⟨ sym $ suc-⟦⟧ _ ⟩
      sucℤ  ⟦ pos' n   +' y  ⟧  ≡[ i ]⟨ sucℤ $ isHom+ (pos' n) y i ⟩
      sucℤ (⟦ pos' n ⟧ + ⟦ y ⟧) ≡⟨ +sucℤ ⟦ pos' n ⟧ ⟦ y ⟧ ⟩
      sucℤ  ⟦ pos' n ⟧ + ⟦ y ⟧  ∎
    isHom+ (negsuc' zero) y = sucℤ-inj _ _
                              ( suc-⟦⟧ (negsuc' zero +' y)
                              ∙ (cong ⟦_⟧ $ Int.sucInt+ (negsuc' zero) y ∙ Int.+-identityˡ y)
                              ∙ sym (+-identityˡ ⟦ y ⟧)
                              ∙ (λ i → suc-identity 0 0 (~ i) + ⟦ y ⟧)
                              ∙ sym (+sucℤ -1 ⟦ y ⟧))
    isHom+ (negsuc' (suc n)) y = cong ⟦_⟧ (sym (Int.predInt+ (negsuc' n) y))
                               ∙ (sym $ pred-⟦⟧ (negsuc' n +' y))
                               ∙ (λ i → predℤ $ isHom+ (negsuc' n) y i)
                               ∙ +predℤ [ 0 , suc n ] ⟦ y ⟧

    isHom· : ∀ x y → ⟦ x ·' y ⟧ ≡ ⟦ x ⟧ · ⟦ y ⟧
    isHom· (Int.pos zero) y = cong ⟦_⟧ (Int.signed-zero (sgn' y)) ∙ sym (·-nullifiesˡ ⟦ y ⟧)
    isHom· (pos' (suc n)) y =
      ⟦ pos' (suc n)     ·'  y ⟧ ≡⟨ cong ⟦_⟧ $ Int.·-pos-suc n y ⟩
      ⟦ y   +'  pos' n   ·'  y ⟧ ≡⟨ isHom+ y _ ⟩
      ⟦ y ⟧ + ⟦ pos' n   ·'  y ⟧ ≡[ i ]⟨ ⟦ y ⟧ + isHom· (pos' n) y i ⟩
      ⟦ y ⟧ + ⟦ pos' n ⟧ · ⟦ y ⟧ ≡⟨ sym $ ·-pos-suc ⟦ pos' n ⟧ ⟦ y ⟧ ⟩
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
      -  ⟦ y ⟧ + ⟦ negsuc' n ⟧ · ⟦ y ⟧ ≡⟨ sym (·-neg-suc ⟦ negsuc' n ⟧ ⟦ y ⟧) ⟩
      predℤ ⟦ negsuc' n ⟧ · ⟦ y ⟧      ∎

  DiffIntΣraw : TypeWithStr ℓ-zero RawRingStructure
  DiffIntΣraw = DiffInt , _+_ , 1 , _·_

  Int≃DiffInt-Σraw : IntΣraw ≃[ RawRingEquivStr ] DiffIntΣraw
  Int≃DiffInt-Σraw = ((_ , ⟦⟧-isEquiv) , (isHom+ , pres1 , isHom·))

  DiffInt-CommRingAxioms : CommRingAxioms DiffInt (str DiffIntΣraw)
  DiffInt-CommRingAxioms = transferAxioms {S = RawRingStructure} rawRingUnivalentStr {axioms = CommRingAxioms} (CommRing→CommRingΣ IntAsCommRing) DiffIntΣraw Int≃DiffInt-Σraw

  DiffIntΣ : TypeWithStr _ CommRingStructure
  DiffIntΣ = (typ DiffIntΣraw) , (str DiffIntΣraw) , DiffInt-CommRingAxioms

  DiffIntAsCommRing : CommRing
  DiffIntAsCommRing = CommRingΣ→CommRing DiffIntΣ

  Int≃DiffInt-CommRingEquiv : Σ[ e ∈ ⟨ IntAsCommRing ⟩ ≃ ⟨ DiffIntAsCommRing ⟩ ] CommRingEquiv IntAsCommRing DiffIntAsCommRing e
  Int≃DiffInt-CommRingEquiv .fst = _ , ⟦⟧-isEquiv
  Int≃DiffInt-CommRingEquiv .snd = ringequiv pres1 isHom+ isHom·

  Int≡DiffInt-AsCommRing : IntAsCommRing ≡ DiffIntAsCommRing
  Int≡DiffInt-AsCommRing = CommRingPath _ _ .fst Int≃DiffInt-CommRingEquiv

DiffInt≡BiInvInt-AsCommRing : DiffIntAsCommRing ≡ BiInvIntAsCommRing
DiffInt≡BiInvInt-AsCommRing = sym Int≡DiffInt-AsCommRing ∙ Int≡BiInvInt-AsCommRing
