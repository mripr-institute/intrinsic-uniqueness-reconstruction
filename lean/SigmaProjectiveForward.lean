import SigmaProjective

namespace Sigma
noncomputable section
open Filter Set
open scoped Topology

def projectiveModel (t : ℝ) : ℝ := 1 / t - 1

theorem projectiveModel_injective : Function.Injective projectiveModel := by
  intro s t he
  have hh : s⁻¹ = t⁻¹ := by
    unfold projectiveModel at he
    simpa only [one_div] using (sub_left_inj.mp he)
  exact inv_injective hh

theorem projectiveModel_cross_ratio {x₁ x₂ x₃ x₄ : ℝ}
    (h1 : 0 < x₁) (h2 : 0 < x₂) (h3 : 0 < x₃) (h4 : 0 < x₄)
    (h14 : x₁ ≠ x₄) (h23 : x₂ ≠ x₃) :
    projectiveCrossRatio (projectiveModel x₁) (projectiveModel x₂)
      (projectiveModel x₃) (projectiveModel x₄) = projectiveCrossRatio x₁ x₂ x₃ x₄ := by
  unfold projectiveCrossRatio
  apply (div_eq_div_iff
    (mul_ne_zero (sub_ne_zero.mpr (projectiveModel_injective.ne h14))
      (sub_ne_zero.mpr (projectiveModel_injective.ne h23)))
    (mul_ne_zero (sub_ne_zero.mpr h14) (sub_ne_zero.mpr h23))).mpr
  unfold projectiveModel
  field_simp
  <;> ring

theorem projectiveModel_preserves_cross_ratios : PreservesPositiveCrossRatios projectiveModel := by
  intro x₁ h1 x₂ h2 x₃ h3 x₄ h4 _ _ h14 h23 _ _
  exact projectiveModel_cross_ratio h1 h2 h3 h4 h14 h23

theorem projectiveModel_three_marks :
    projectiveModel 1 = 0 ∧ projectiveModel 2 = -1 / 2 ∧ projectiveModel 3 = -2 / 3 := by
  norm_num [projectiveModel]

theorem projectiveModel_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt projectiveModel (-(1 / t ^ (2 : ℕ))) t := reciprocal_hasDerivAt ht

theorem projectiveModel_first_derivative {t : ℝ} (ht : 0 < t) :
    deriv projectiveModel t = -(1 / t ^ (2 : ℕ)) := (projectiveModel_hasDerivAt ht).deriv

theorem projectiveModel_second_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt (deriv projectiveModel) (2 / t ^ (3 : ℕ)) t := by
  have hd := ((hasDerivAt_const t (1 : ℝ)).div ((hasDerivAt_id t).pow 2)
    (pow_ne_zero _ (ne_of_gt ht))).neg
  have hh : HasDerivAt (fun x : ℝ => -(1 / x ^ (2 : ℕ))) (2 / t ^ (3 : ℕ)) t := by
    convert hd using 1
    field_simp
    <;> ring
  apply hh.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
  exact projectiveModel_first_derivative hx

theorem projectiveModel_second_derivative {t : ℝ} (ht : 0 < t) :
    deriv (deriv projectiveModel) t = 2 / t ^ (3 : ℕ) :=
  (projectiveModel_second_hasDerivAt ht).deriv

theorem projectiveModel_third_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt (deriv (deriv projectiveModel)) (-6 / t ^ (4 : ℕ)) t := by
  have hd := (hasDerivAt_const t (2 : ℝ)).div ((hasDerivAt_id t).pow 3)
    (pow_ne_zero _ (ne_of_gt ht))
  have hh : HasDerivAt (fun x : ℝ => 2 / x ^ (3 : ℕ)) (-6 / t ^ (4 : ℕ)) t := by
    convert hd using 1
    field_simp
    <;> ring
  apply hh.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
  exact projectiveModel_second_derivative hx

theorem projectiveModel_third_derivative {t : ℝ} (ht : 0 < t) :
    deriv (deriv (deriv projectiveModel)) t = -6 / t ^ (4 : ℕ) :=
  (projectiveModel_third_hasDerivAt ht).deriv

theorem projectiveModel_schwarzian_zero {t : ℝ} (ht : 0 < t) :
    projectiveSchwarzian projectiveModel t = 0 := by
  unfold projectiveSchwarzian
  rw [projectiveModel_first_derivative ht, projectiveModel_second_derivative ht,
    projectiveModel_third_derivative ht]
  field_simp
  <;> ring

theorem projectiveModel_C3 : ContDiffOn ℝ 3 projectiveModel (Ioi 0) := by
  exact (contDiffOn_const.div contDiffOn_id (fun t ht => ne_of_gt ht)).sub contDiffOn_const

theorem projectiveModel_schwarzian_marks :
    projectiveModel 1 = 0 ∧ deriv projectiveModel 1 = -1 ∧
      deriv (deriv projectiveModel) 1 = 2 ∧
      ∀ t > 0, deriv projectiveModel t ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [projectiveModel]
  · rw [projectiveModel_first_derivative (by norm_num)]
    norm_num
  · rw [projectiveModel_second_derivative (by norm_num)]
    norm_num
  · intro t ht
    rw [projectiveModel_first_derivative ht]
    exact neg_ne_zero.mpr (one_div_ne_zero (pow_ne_zero _ (ne_of_gt ht)))

/-- A projective, zero-Schwarzian map retaining the first two Schwarzian marks
but differing from the calibrated model. -/
def projectiveAffineCounter (t : ℝ) : ℝ := 1 - t

theorem projectiveAffineCounter_injective : Function.Injective projectiveAffineCounter := by
  intro s t he
  exact sub_right_inj.mp he

theorem projectiveAffineCounter_preserves_cross_ratios :
    PreservesPositiveCrossRatios projectiveAffineCounter := by
  intro x₁ h1 x₂ h2 x₃ h3 x₄ h4 _ _ _ _ _ _
  unfold projectiveCrossRatio projectiveAffineCounter
  congr 1 <;> ring

theorem projectiveAffineCounter_deriv : deriv projectiveAffineCounter = fun _ => -1 := by
  funext t
  exact ((hasDerivAt_id t).const_sub 1).deriv

theorem projectiveAffineCounter_second_deriv :
    deriv (deriv projectiveAffineCounter) = fun _ => 0 := by
  rw [projectiveAffineCounter_deriv]
  funext t
  exact (hasDerivAt_const t (-1 : ℝ)).deriv

theorem projectiveAffineCounter_third_deriv :
    deriv (deriv (deriv projectiveAffineCounter)) = fun _ => 0 := by
  rw [projectiveAffineCounter_second_deriv]
  funext t
  exact (hasDerivAt_const t (0 : ℝ)).deriv

theorem projectiveAffineCounter_schwarzian_data :
    ContDiffOn ℝ 3 projectiveAffineCounter (Ioi 0) ∧
    projectiveAffineCounter 1 = 0 ∧ deriv projectiveAffineCounter 1 = -1 ∧
    (∀ t > 0, deriv projectiveAffineCounter t ≠ 0) ∧
    (∀ t > 0, projectiveSchwarzian projectiveAffineCounter t = 0) := by
  refine ⟨contDiffOn_const.sub contDiffOn_id, ?_, ?_, ?_, ?_⟩
  · norm_num [projectiveAffineCounter]
  · rw [projectiveAffineCounter_deriv]
  · intro t ht
    simp [projectiveAffineCounter_deriv]
  · intro t ht
    simp [projectiveSchwarzian, projectiveAffineCounter_deriv,
      projectiveAffineCounter_second_deriv, projectiveAffineCounter_third_deriv]

theorem projectiveAffineCounter_not_model :
    ¬ ∀ t > 0, projectiveAffineCounter t = projectiveModel t := by
  intro he
  have hh := he 2 (by norm_num)
  norm_num [projectiveAffineCounter, projectiveModel] at hh

end
end Sigma
