import SigmaRealProjectiveDoubleTriviality
import SigmaRealProjectiveRationalWitness

namespace Sigma
noncomputable section
open FiniteComplexBundle

/-- The nonzero reduced native K⁰ class of the complexified tautological
line has additive order two, proved by an actual bundle trivialization. -/
theorem real_projective_reduced_k0_two_torsion :
    kClass realProjectiveKLine - kClass (FiniteComplexBundle.trivial 1) ≠ 0 ∧
      (2 : ℕ) • (kClass realProjectiveKLine - kClass (FiniteComplexBundle.trivial 1)) = 0 := by
  constructor
  · exact sub_ne_zero.mpr real_projective_complex_k0_class_ne_one
  · rw [nsmul_sub, two_nsmul, two_nsmul, real_projective_k0_double_eq, sub_self]

/-- Every rational additive characteristic of the actual native K⁰ group
has the same value on these two fixed-base lines. This proves the rational
obstruction without assuming any RP² cohomology calculation or Chern value. -/
theorem real_projective_rational_additive_characteristic_eq
    {H : Type*} [AddCommGroup H] [Module ℚ H]
    (χ : K0 RealProjectivePlane →+ H) :
    χ (kClass realProjectiveKLine) = χ (kClass (FiniteComplexBundle.trivial 1)) := by
  have he := congrArg χ real_projective_k0_double_eq
  simp only [map_add] at he
  have htwo : (2 : ℚ) • χ (kClass realProjectiveKLine) =
      (2 : ℚ) • χ (kClass (FiniteComplexBundle.trivial 1)) := by
    simpa only [two_smul] using he
  have hhalf := congrArg (fun z : H => (1 / 2 : ℚ) • z) htwo
  simpa only [smul_smul, one_div_mul_cancel (by norm_num : (2 : ℚ) ≠ 0), one_smul] using hhalf

/-- The usual Chern character has precisely these primitive properties:
additivity on native K⁰ and the trivial-line normalization. The conclusion
holds in every supplied rational cohomology ring, independently of its
presentation. No input states a characteristic value of the RP² line. -/
theorem real_projective_normalized_rational_characteristic_one
    {H : Type*} [CommRing H] [Algebra ℚ H]
    (ch : K0 RealProjectivePlane →+ H)
    (hunit : ch (kClass (FiniteComplexBundle.trivial 1)) = 1) :
    ch (kClass realProjectiveKLine) = 1 :=
  (real_projective_rational_additive_characteristic_eq ch).trans hunit

/-- The entire fixed-base F5 obstruction: integral K⁰ classes differ, while
every rational additive characteristic (in particular the ordinary Chern
character) agrees. The native nontriviality and tensor-square trivialization
are proved in the imported bundle modules. -/
theorem real_projective_fixed_base_integral_rational_witness
    {H : Type*} [AddCommGroup H] [Module ℚ H]
    (χ : K0 RealProjectivePlane →+ H) :
    kClass realProjectiveKLine ≠ kClass (FiniteComplexBundle.trivial 1) ∧
      χ (kClass realProjectiveKLine) = χ (kClass (FiniteComplexBundle.trivial 1)) :=
  ⟨real_projective_complex_k0_class_ne_one,
    real_projective_rational_additive_characteristic_eq χ⟩

/-- Keeping an arbitrary entire scalar object and every other packet fixed
does not repair the loss. The rational target may itself be a product of
all the supplied rational additive characteristic observations. -/
theorem real_projective_scalar_rational_data_no_k0_decoder
    {S H : Type*} [AddCommGroup H] [Module ℚ H]
    (χ : K0 RealProjectivePlane →+ H) (s : S) :
    ¬ ∃ decode : S × H → K0 RealProjectivePlane,
      ∀ V : FiniteComplexBundle RealProjectivePlane,
        decode (s, χ (kClass V)) = kClass V := by
  rintro ⟨decode, hd⟩
  apply real_projective_complex_k0_class_ne_one
  rw [← hd realProjectiveKLine, real_projective_rational_additive_characteristic_eq,
    hd (FiniteComplexBundle.trivial 1)]

/-- Under the usual supplied classification of complex lines by their
integral first Chern class, the two integral classes differ. The hypothesis
is the general identifying law for every pair of native rank-one bundles;
it supplies no RP²-specific class value or nonvanishing assertion. -/
theorem real_projective_integral_line_characteristic_ne
    {H : Type*} (c : FiniteComplexBundle RealProjectivePlane → H)
    (hclassify : ∀ V W : FiniteComplexBundle RealProjectivePlane,
      Module.finrank ℂ V.Model = 1 → Module.finrank ℂ W.Model = 1 →
      c V = c W → Nonempty (Iso V W)) :
    c realProjectiveKLine ≠ c (FiniteComplexBundle.trivial 1) := by
  intro he
  obtain ⟨e⟩ := hclassify realProjectiveKLine (FiniteComplexBundle.trivial 1)
    (by change Module.finrank ℂ (Fin 1 → ℂ) = 1; simp)
    (by change Module.finrank ℂ (Fin 1 → ℂ) = 1; simp) he
  exact real_projective_complex_k0_class_ne_one (kClass_iso e)

theorem real_projective_integral_characteristic_no_decoder
    {S H : Type*} (c : FiniteComplexBundle RealProjectivePlane → H)
    (hclassify : ∀ V W : FiniteComplexBundle RealProjectivePlane,
      Module.finrank ℂ V.Model = 1 → Module.finrank ℂ W.Model = 1 →
      c V = c W → Nonempty (Iso V W)) (s : S) :
    ¬ ∃ decode : S → H, ∀ V : FiniteComplexBundle RealProjectivePlane,
      Module.finrank ℂ V.Model = 1 → decode s = c V := by
  rintro ⟨decode, hd⟩
  apply real_projective_integral_line_characteristic_ne c hclassify
  exact (hd realProjectiveKLine (by change Module.finrank ℂ (Fin 1 → ℂ) = 1; simp)).symm.trans
    (hd (FiniteComplexBundle.trivial 1) (by change Module.finrank ℂ (Fin 1 → ℂ) = 1; simp))

end
end Sigma
