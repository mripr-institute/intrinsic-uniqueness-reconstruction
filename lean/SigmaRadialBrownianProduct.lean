import SigmaRadialBrownianMoments

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal

theorem probability_pi_coordinate_law {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (i : ι) :
    (Measure.pi μ).map (fun x : ι → ℝ => x i) = μ i := by
  classical
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_pi_apply i) hs]
  have he : (fun x : ι → ℝ => x i) ⁻¹' s =
      Set.pi Set.univ (Function.update (fun _ => Set.univ) i s) := by
    ext x
    constructor
    · intro hx k _
      by_cases hk : k = i
      · subst k; simpa using hx
      · simp [Function.update, hk]
    · intro hx
      simpa using hx i (Set.mem_univ i)
  rw [he, Measure.pi_pi]
  simp only [Function.update_apply, apply_ite, measure_univ]
  simp

theorem probability_pi_coordinate_independent {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] :
    Pairwise (fun i j => IndepFun (fun x : ι → ℝ => x i)
      (fun x : ι → ℝ => x j) (Measure.pi μ)) := by
  classical
  intro i j hij
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro s t hs ht
  have he : (fun x : ι → ℝ => x i) ⁻¹' s ∩ (fun x : ι → ℝ => x j) ⁻¹' t =
      Set.pi Set.univ (Function.update (Function.update (fun _ => Set.univ) i s) j t) := by
    ext x
    constructor
    · rintro ⟨hx, hy⟩ k _
      by_cases hkj : k = j
      · subst k; simpa using hy
      · by_cases hki : k = i
        · subst k; simpa [Function.update, hij] using hx
        · simp [Function.update, hki, hkj]
    · intro hx
      exact ⟨by simpa [Function.update, hij] using hx i (Set.mem_univ i),
        by simpa using hx j (Set.mem_univ j)⟩
  rw [he, Measure.pi_pi,
    ← Measure.map_apply (measurable_pi_apply i) hs, probability_pi_coordinate_law,
    ← Measure.map_apply (measurable_pi_apply j) ht, probability_pi_coordinate_law]
  calc
    _ = (∏ k : ι, if k = i then (μ i) s else 1) *
        (∏ k : ι, if k = j then (μ j) t else 1) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro k _
      by_cases hki : k = i
      · subst k; simp [Function.update, hij]
      · by_cases hkj : k = j
        · subst k; simp [Function.update, hij.symm]
        · simp [Function.update, hki, hkj]
    _ = _ := by simp

theorem radial_brownian_gaussian_norm_square_identDistrib (D : ℕ) (v : ℝ≥0) :
    IdentDistrib (fun x : Fin D → ℝ => ∑ i, x i ^ 2)
      (fun z : EuclideanSpace ℝ (Fin D) => ‖z‖ ^ 2)
      (Measure.pi (fun _ : Fin D => gaussianReal 0 v)) (radialBrownianGaussian D v) := by
  have h : IdentDistrib (EuclideanSpace.measurableEquiv (Fin D)).symm
      (fun z : EuclideanSpace ℝ (Fin D) => z)
      (Measure.pi (fun _ : Fin D => gaussianReal 0 v)) (radialBrownianGaussian D v) :=
    ⟨(EuclideanSpace.measurableEquiv (Fin D)).symm.measurable.aemeasurable,
      measurable_id.aemeasurable, by simp [radialBrownianGaussian]⟩
  have hn := h.comp (measurable_norm.pow_const 2)
  convert hn using 1
  funext x
  simp [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs]
  rfl

theorem radial_brownian_gaussian_norm_square_memLp (D : ℕ) (v : ℝ≥0) :
    Memℒp (fun z : EuclideanSpace ℝ (Fin D) => ‖z‖ ^ 2) 2
      (radialBrownianGaussian D v) := by
  apply (radial_brownian_gaussian_norm_square_identDistrib D v).memℒp_snd
  apply memℒp_finset_sum
  intro i _
  exact (gaussian_square_identDistrib (measurable_pi_apply i) v
    (probability_pi_coordinate_law (fun _ : Fin D => gaussianReal 0 v) i)).symm.memℒp_snd
      (gaussian_zero_square_memLp v)

theorem radial_brownian_gaussian_norm_square_mean (D : ℕ) (v : ℝ≥0) :
    (∫ z : EuclideanSpace ℝ (Fin D), ‖z‖ ^ 2 ∂radialBrownianGaussian D v) =
      (D : ℝ) * (v : ℝ) := by
  rw [← (radial_brownian_gaussian_norm_square_identDistrib D v).integral_eq,
    gaussian_square_sum_mean _ _ (fun _ : Fin D => v)
      (fun i => measurable_pi_apply i)
      (fun i => probability_pi_coordinate_law (fun _ : Fin D => gaussianReal 0 v) i)]
  simp

theorem radial_brownian_gaussian_norm_square_variance (D : ℕ) (v : ℝ≥0) :
    variance (fun z : EuclideanSpace ℝ (Fin D) => ‖z‖ ^ 2)
      (radialBrownianGaussian D v) = 2 * (D : ℝ) * (v : ℝ) ^ 2 := by
  rw [← (radial_brownian_gaussian_norm_square_identDistrib D v).variance_eq,
    gaussian_square_sum_variance _ _ (fun _ : Fin D => v)
      (fun i => measurable_pi_apply i)
      (fun i => probability_pi_coordinate_law (fun _ : Fin D => gaussianReal 0 v) i)
      (probability_pi_coordinate_independent (fun _ : Fin D => gaussianReal 0 v))]
  simp [mul_assoc, mul_left_comm]

end
end Sigma
