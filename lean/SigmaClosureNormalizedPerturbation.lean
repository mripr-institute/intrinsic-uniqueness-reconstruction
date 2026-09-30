import SigmaClosurePerturbation
import SigmaProbGamma
import SigmaProbInvolutionBoundary

namespace Sigma.Closure
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

private theorem gamma_nonnegative_ae : ∀ᵐ t ∂gammaProbability, 0 ≤ t := by
  rw [ae_iff]
  simpa only [not_le] using gamma_probability_negative_ray

private theorem gamma_ne_one_ae : ∀ᵐ t ∂gammaProbability, t ≠ (1 : ℝ) := by
  rw [ae_iff]
  simpa using gamma_probability_no_atom 1

private theorem perturbation_positive_ae (b : ℝ) :
    ∀ᵐ t ∂gammaProbability, 0 < perturbation b t := by
  filter_upwards [gamma_ne_one_ae] with t ht
  have hn : t - 1 ≠ 0 := sub_ne_zero.mpr ht
  unfold perturbation
  positivity

private theorem perturbation_bounded (b : ℝ) (hb : 0 < b) :
    ∃ C > 0, ∀ t ≥ 0, |perturbation b t| ≤ C := by
  apply positive_ray_bound_of_decay
  · unfold perturbation
    fun_prop
  · exact perturbation_tendsto_atTop b hb

private def gBound : ℝ := (perturbation_bounded 1 (by norm_num)).choose
private def hBound : ℝ := (perturbation_bounded 2 (by norm_num)).choose

private theorem g_bound_pos : 0 < gBound := (perturbation_bounded 1 (by norm_num)).choose_spec.1
private theorem h_bound_pos : 0 < hBound := (perturbation_bounded 2 (by norm_num)).choose_spec.1

private theorem g_bound (t : ℝ) (ht : 0 ≤ t) : |perturbation 1 t| ≤ gBound :=
  (perturbation_bounded 1 (by norm_num)).choose_spec.2 t ht

private theorem h_bound (t : ℝ) (ht : 0 ≤ t) : |perturbation 2 t| ≤ hBound :=
  (perturbation_bounded 2 (by norm_num)).choose_spec.2 t ht

def perturbationWeight (ε δ t : ℝ) : ℝ :=
  Real.exp (-ε * perturbation 1 t - δ * perturbation 2 t)

def perturbationMass (ε δ : ℝ) : ℝ := ∫ t, perturbationWeight ε δ t ∂gammaProbability

private theorem perturbation_weight_bound (ε δ t : ℝ) (ht : 0 ≤ t) :
    ‖perturbationWeight ε δ t‖ ≤ Real.exp (|ε| * gBound + |δ| * hBound) := by
  rw [perturbationWeight, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hg := (neg_le_abs (ε * perturbation 1 t)).trans
    (by simpa [abs_mul] using mul_le_mul_of_nonneg_left (g_bound t ht) (abs_nonneg ε))
  have hh := (neg_le_abs (δ * perturbation 2 t)).trans
    (by simpa [abs_mul] using mul_le_mul_of_nonneg_left (h_bound t ht) (abs_nonneg δ))
  linarith

theorem perturbation_weight_integrable (ε δ : ℝ) :
    Integrable (perturbationWeight ε δ) gammaProbability := by
  apply (integrable_const (Real.exp (|ε| * gBound + |δ| * hBound))).mono'
  · exact (show Continuous (perturbationWeight ε δ) by unfold perturbationWeight perturbation; fun_prop).aestronglyMeasurable
  · filter_upwards [gamma_nonnegative_ae] with t ht
    exact perturbation_weight_bound ε δ t ht

/-- Bounded perturbations justify continuity of the actual mass integral. -/
theorem perturbation_mass_continuous :
    Continuous (fun z : ℝ × ℝ => perturbationMass z.1 z.2) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  let C := Real.exp ((|z.1| + 1) * gBound + (|z.2| + 1) * hBound)
  apply continuousAt_of_dominated (bound := fun _ => C)
  · exact Eventually.of_forall (fun w => (perturbation_weight_integrable w.1 w.2).aestronglyMeasurable)
  · have he : ∀ᶠ w : ℝ × ℝ in 𝓝 z, |w.1| < |z.1| + 1 :=
      continuousAt_fst.abs.eventually (gt_mem_nhds (lt_add_one _))
    have hd : ∀ᶠ w : ℝ × ℝ in 𝓝 z, |w.2| < |z.2| + 1 :=
      continuousAt_snd.abs.eventually (gt_mem_nhds (lt_add_one _))
    filter_upwards [he, hd] with w hw1 hw2
    filter_upwards [gamma_nonnegative_ae] with t ht
    apply (perturbation_weight_bound w.1 w.2 t ht).trans
    exact Real.exp_le_exp.mpr (add_le_add
      (mul_le_mul_of_nonneg_right hw1.le g_bound_pos.le)
      (mul_le_mul_of_nonneg_right hw2.le h_bound_pos.le))
  · exact integrable_const C
  · exact Eventually.of_forall (fun t => by unfold perturbationWeight; fun_prop)

theorem perturbation_mass_zero : perturbationMass 0 0 = 1 := by
  simp [perturbationMass, perturbationWeight]

theorem perturbation_mass_positive_scale_lt_one (ε : ℝ) (hε : 0 < ε) :
    perturbationMass ε 0 < 1 := by
  have hi := (integrable_const (1 : ℝ)).sub (perturbation_weight_integrable ε 0)
  have hp : 0 < ∫ t, 1 - perturbationWeight ε 0 t ∂gammaProbability := by
    apply probability_integral_pos_of_ae_pos _ hi
    filter_upwards [perturbation_positive_ae 1] with t ht
    apply sub_pos.mpr
    rw [perturbationWeight, zero_mul, sub_zero]
    exact Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos hε) ht)
  rw [integral_sub (integrable_const _) (perturbation_weight_integrable ε 0)] at hp
  simpa [perturbationMass] using hp

theorem perturbation_mass_negative_offset_gt_one (δ : ℝ) (hδ : δ < 0) :
    1 < perturbationMass 0 δ := by
  have hi := (perturbation_weight_integrable 0 δ).sub (integrable_const (1 : ℝ))
  have hp : 0 < ∫ t, perturbationWeight 0 δ t - 1 ∂gammaProbability := by
    apply probability_integral_pos_of_ae_pos _ hi
    filter_upwards [perturbation_positive_ae 2] with t ht
    apply sub_pos.mpr
    rw [perturbationWeight, neg_zero, zero_mul, zero_sub]
    exact Real.one_lt_exp_iff.mpr (neg_pos.mpr (mul_neg_of_neg_of_pos hδ ht))
  rw [integral_sub (perturbation_weight_integrable 0 δ) (integrable_const _)] at hp
  simpa [perturbationMass] using hp

/-- The intermediate-value theorem selects a nonzero, arbitrarily small
mass-preserving perturbation. Continuity and strict mass inequalities were
proved for the actual integral, so no implicit-function input is needed. -/
theorem normalized_perturbation_parameters (η : ℝ) (hη : 0 < η) :
    ∃ ε δ : ℝ, 0 < ε ∧ ε < η ∧ |δ| < η ∧ perturbationMass ε δ = 1 := by
  let d := -η / 2
  have hd : d < 0 := by dsimp [d]; linarith only [hη]
  have hc : Continuous (fun ε : ℝ => perturbationMass ε d) :=
    Continuous.comp (g := fun z : ℝ × ℝ => perturbationMass z.1 z.2)
      (f := fun ε : ℝ => (ε, d)) perturbation_mass_continuous
      (show Continuous (fun ε : ℝ => (ε, d)) from continuous_id.prod_mk continuous_const)
  have hn : ∀ᶠ ε : ℝ in 𝓝 0, 1 < perturbationMass ε d :=
    hc.continuousAt.eventually (lt_mem_nhds (perturbation_mass_negative_offset_gt_one d hd))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hn
  let ε := min (r / 2) (η / 2)
  have he : 0 < ε := lt_min (by linarith) (by linarith)
  have her : ε < r := (min_le_left _ _).trans_lt (by linarith)
  have heη : ε < η := (min_le_right _ _).trans_lt (by linarith)
  have hleft : 1 < perturbationMass ε d := hball (by simpa [Real.dist_eq, abs_of_pos he] using her)
  have hright : perturbationMass ε 0 < 1 := perturbation_mass_positive_scale_lt_one ε he
  have hcont : ContinuousOn (perturbationMass ε) (Icc d 0) :=
    (Continuous.comp (g := fun z : ℝ × ℝ => perturbationMass z.1 z.2)
      (f := fun δ : ℝ => (ε, δ)) perturbation_mass_continuous
      (show Continuous (fun δ : ℝ => (ε, δ)) from continuous_const.prod_mk continuous_id)).continuousOn
  obtain ⟨δ, hδ, hm⟩ := intermediate_value_Icc' hd.le hcont ⟨hright.le, hleft.le⟩
  refine ⟨ε, δ, he, heη, ?_, hm⟩
  rw [abs_of_nonpos hδ.2]
  have hlow := hδ.1
  dsimp [d] at hlow
  linarith

theorem perturbation_mass_integral (ε δ : ℝ) :
    perturbationMass ε δ =
      ∫ t : ℝ in Ioi 0, Real.exp (-1 - perturbedIntrinsic ε δ t) := by
  rw [perturbationMass, gamma_probability_integral]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [SigmaPresentations.density_eq_exp_potential ht]
  unfold perturbationWeight perturbedIntrinsic
  rw [← Real.exp_add]
  congr 1
  ring

/-- The paper's normalized intrinsic deletion witness, including analyticity,
strict convexity, all three anchors, exact mass, both endpoint limits and a
genuine difference on the positive ray. -/
theorem normalized_intrinsic_deletion_witness :
    ∃ J : ℝ → ℝ,
      (∀ t > 0, AnalyticAt ℝ J t) ∧
      StrictConvexOn ℝ (Ioi 0) J ∧
      J 1 = 0 ∧ deriv J 1 = 0 ∧ deriv (deriv J) 1 = 1 ∧
      (∫ t : ℝ in Ioi 0, Real.exp (-1 - J t)) = 1 ∧
      Tendsto J (𝓝[>] (0 : ℝ)) atTop ∧ Tendsto J atTop atTop ∧
      ¬ (∀ t > 0, J t = I t) := by
  obtain ⟨η, hη, hconvex⟩ := perturbed_intrinsic_strictConvex_near_zero
  obtain ⟨ε, δ, he, heη, hδ, hm⟩ := normalized_perturbation_parameters η hη
  have ha := perturbed_intrinsic_anchors ε δ
  have hl := perturbed_intrinsic_endpoint_divergence ε δ
  refine ⟨perturbedIntrinsic ε δ, fun _ ht => perturbed_intrinsic_analytic ε δ ht,
    hconvex ε δ (by simpa [abs_of_pos he] using heη) hδ,
    ha.1, ha.2.1, ha.2.2, ?_, hl.1, hl.2, ?_⟩
  · rwa [← perturbation_mass_integral]
  · intro hid
    exact he.ne' ((perturbed_intrinsic_identical_iff ε δ).mp hid).1

end
end Sigma.Closure
