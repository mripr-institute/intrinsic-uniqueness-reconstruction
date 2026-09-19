import SigmaArithmeticDivisors
import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.Analytic.Constructions

namespace Sigma
noncomputable section
open scoped BigOperators

section Totient
variable {M : Type*} [CommMonoid M] (E : ℕ+ ≃* M)

/-- Totient retains the numerical labels and their sizes. -/
def labelledTotient (x : M) : ℕ := Nat.totient (E.symm x).val

theorem labelled_totient_one : labelledTotient E 1=1 := by
  simp [labelledTotient]

theorem labelled_totient_formula (x : M) :
    labelledTotient E x=(E.symm x).val.factorization.prod
      (fun p a => p^(a-1)*(p-1)) :=
  Nat.totient_eq_prod_factorization (E.symm x).ne_zero

theorem labelled_totient_residue_count (x : M) :
    labelledTotient E x=Nat.card {a : ℕ // a < (E.symm x).val ∧
      Nat.Coprime (E.symm x).val a} :=
  Nat.totient_eq_card_lt_and_coprime _

/-- Equivalent residue representatives 1 through n, as in the paper. -/
theorem labelled_totient_positive_residue_count (x : M) :
    labelledTotient E x=
      ((Finset.Ico 1 (1+(E.symm x).val)).filter
        (fun a => Nat.Coprime (E.symm x).val a)).card := by
  simpa only [add_comm] using (Nat.filter_coprime_Ico_eq_totient (E.symm x).val 1).symm

theorem prime_swap_changes_totient :
    Nat.totient (swapTwoThree 2).val ≠ Nat.totient (2:ℕ+) := by
  rw [swap_two_three_two]
  decide

end Totient

/-- Reflexive divisibility on the original nonunital image is exactly
equality or multiplication by another original image point. -/
theorem original_image_reflexive_divisibility {A : Type*} [Semigroup A] (a b : A) :
    (WithOne.coe a : WithOne A) ∣ WithOne.coe b ↔
      a=b ∨ ∃ z : A, b=a*z := by
  constructor
  · rintro ⟨z,hz⟩
    induction z using WithOne.recOneCoe with
    | h₁ =>
      left
      apply WithOne.coe_inj.mp
      simpa using hz.symm
    | h₂ z =>
      right
      exact ⟨z, WithOne.coe_inj.mp hz⟩
  · rintro (rfl | ⟨z,rfl⟩)
    · exact dvd_rfl
    · exact ⟨WithOne.coe z,rfl⟩

/-- Coprime original labels require the separately adjoined unit as gcd. -/
theorem labelled_coprime_gcd_is_unit {M : Type*} [CommMonoid M] (E : ℕ+ ≃* M) :
    labelledGcd E (E 2) (E 3)=1 := by
  have h : PNat.gcd 2 3=1 := by
    apply Subtype.ext
    norm_num [PNat.gcd]
  simp only [labelledGcd, E.symm_apply_apply, h, map_one]

/-- Two injective encodings carry the same labelled multiplication regardless
of the values or analytic shapes of the encodings. -/
def labelledImageChangeEquiv {B C : Type*} (e : IntegerCodeIndex → B)
    (f : IntegerCodeIndex → C) (he : Function.Injective e) (hf : Function.Injective f) :
    letI := (Equiv.ofInjective e he).symm.commSemigroup
    letI := (Equiv.ofInjective f hf).symm.commSemigroup
    WithOne (Set.range e) ≃* WithOne (Set.range f) := by
  letI := (Equiv.ofInjective e he).symm.commSemigroup
  letI := (Equiv.ofInjective f hf).symm.commSemigroup
  exact (labelledImageEquiv e he).symm.trans (labelledImageEquiv f hf)

theorem labelled_image_change_preserves_labels {B C : Type*} (e : IntegerCodeIndex → B)
    (f : IntegerCodeIndex → C) (he : Function.Injective e) (hf : Function.Injective f)
    (a : IntegerCodeIndex) :
    letI := (Equiv.ofInjective e he).symm.commSemigroup
    letI := (Equiv.ofInjective f hf).symm.commSemigroup
    labelledImageChangeEquiv e f he hf (WithOne.coe (codeImagePoint e a))=
      WithOne.coe (codeImagePoint f a) := by
  letI := (Equiv.ofInjective e he).symm.commSemigroup
  letI := (Equiv.ofInjective f hf).symm.commSemigroup
  rw [← labelled_image_encode e he a, ← labelled_image_encode f hf a]
  exact congrArg (labelledImageEquiv f hf) ((labelledImageEquiv e he).symm_apply_apply _)

def linearIntegerCode (n : IntegerCodeIndex) : ℝ := n.val
def squareIntegerCode (n : IntegerCodeIndex) : ℝ := (n.val:ℝ)^2

theorem linear_integer_code_injective : Function.Injective linearIntegerCode := by
  intro a b h
  apply Subtype.ext
  change (a.val:ℝ)=(b.val:ℝ) at h
  exact_mod_cast h

theorem square_integer_code_injective : Function.Injective squareIntegerCode := by
  intro a b h
  apply linear_integer_code_injective
  change (a.val:ℝ)=(b.val:ℝ)
  have ha : 0 ≤ (a.val:ℝ) := Nat.cast_nonneg _
  have hb : 0 ≤ (b.val:ℝ) := Nat.cast_nonneg _
  change (a.val:ℝ)^2=(b.val:ℝ)^2 at h
  nlinarith

/-- Actual distinct analytic coding shapes with identical labelled abstract
monoids, hence also indistinguishable after erasing the integer labels. -/
def analyticCodeCounterexampleEquiv :
    letI := (Equiv.ofInjective linearIntegerCode linear_integer_code_injective).symm.commSemigroup
    letI := (Equiv.ofInjective squareIntegerCode square_integer_code_injective).symm.commSemigroup
    WithOne (Set.range linearIntegerCode) ≃* WithOne (Set.range squareIntegerCode) :=
  labelledImageChangeEquiv _ _ linear_integer_code_injective square_integer_code_injective

theorem analytic_code_counterexample_shapes :
    (∀ x : ℝ, AnalyticAt ℝ (fun t : ℝ => t) x) ∧
    (∀ x : ℝ, AnalyticAt ℝ (fun t : ℝ => t^2) x) ∧
    linearIntegerCode ⟨2,le_rfl⟩ ≠ squareIntegerCode ⟨2,le_rfl⟩ := by
  refine ⟨fun _ => analyticAt_id, fun _ => analyticAt_id.pow 2, ?_⟩
  norm_num [linearIntegerCode, squareIntegerCode]

theorem placed_unit_parameters_injective (c : ℝ) :
    Function.Injective (placedIntegerCode 1 1 c) := by
  intro a b h
  have ha : (((a.val-1:ℕ):ℝ)+2)=(a.val:ℝ)+1 := by
    rw [Nat.cast_sub (by have := a.property; omega)]
    push_cast
    ring
  have hb : (((b.val-1:ℕ):ℝ)+2)=(b.val:ℝ)+1 := by
    rw [Nat.cast_sub (by have := b.property; omega)]
    push_cast
    ring
  have he : SigmaPresentations.H (((a.val-1:ℕ):ℝ)+2)=
      SigmaPresentations.H (((b.val-1:ℕ):ℝ)+2) := by
    rw [ha,hb]
    unfold placedIntegerCode placedCode at h
    unfold SigmaPresentations.H
    simp only [one_mul] at h
    rw [add_comm 1 (a.val:ℝ),add_comm 1 (b.val:ℝ)] at h
    linarith
  have hi := intrinsic_alternative_injective he
  apply Subtype.ext
  have := a.property
  have := b.property
  omega

/-- Even within the paper's placed log-affine family, the abstract monoid
does not recover the real-valued embedding or its additive level. -/
def placedLevelCounterexampleEquiv :
    letI := (Equiv.ofInjective (placedIntegerCode 1 1 0)
      (placed_unit_parameters_injective 0)).symm.commSemigroup
    letI := (Equiv.ofInjective (placedIntegerCode 1 1 1)
      (placed_unit_parameters_injective 1)).symm.commSemigroup
    WithOne (Set.range (placedIntegerCode 1 1 0)) ≃*
      WithOne (Set.range (placedIntegerCode 1 1 1)) :=
  labelledImageChangeEquiv _ _ (placed_unit_parameters_injective 0)
    (placed_unit_parameters_injective 1)

theorem placed_level_counterexample_values :
    placedIntegerCode 1 1 0 ⟨2,le_rfl⟩ ≠ placedIntegerCode 1 1 1 ⟨2,le_rfl⟩ := by
  unfold placedIntegerCode placedCode
  linarith

end
end Sigma
