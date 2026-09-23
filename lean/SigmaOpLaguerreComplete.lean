import SigmaOpLaguerreMomentDensity
import Mathlib.Analysis.InnerProductSpace.l2Space

namespace Sigma
noncomputable section
open MeasureTheory Filter Polynomial
open scoped Topology ENNReal BigOperators

theorem gamma_real_monomial_mem_l2 (n : ℕ) :
    Memℒp (fun t : ℝ => t^n) 2 gammaProbability := by
  apply (memℒp_two_iff_integrable_sq (by fun_prop)).mpr
  simpa only [←pow_mul] using gamma_probability_monomial_integrable (n*2)

theorem gamma_small_exponential_mem_l2 :
    Memℒp (fun t : ℝ => Real.exp ((1/4)*|t|)) 2 gammaProbability := by
  apply (memℒp_two_iff_integrable_sq
    ((continuous_const.mul continuous_id.abs).rexp.aestronglyMeasurable)).mpr
  have hi := operator_factorial_moments_exp_abs_integrable gammaProbability
    gamma_probability_moments (c := 1/2) (by norm_num) (by norm_num)
  convert hi using 1
  ext t
  rw [pow_two, ←Real.exp_add]
  congr 1
  simp only [id_eq]
  ring

theorem gamma_real_l2_zero_of_laguerre (f : ℝ → ℝ)
    (hf : Measurable f) (hf2 : Memℒp f 2 gammaProbability)
    (hL : ∀ n : ℕ, (∫ t : ℝ, f t * opLaguerre n t ∂gammaProbability) = 0) :
    f =ᵐ[gammaProbability] 0 := by
  apply real_mem_l2_zero_of_moments gammaProbability f hf hf2
    gamma_real_monomial_mem_l2 (1/4) (by norm_num) gamma_small_exponential_mem_l2
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have he := hL n
    have hi (k : ℕ) : Integrable (fun t : ℝ =>
        opLaguerreCoefficient n k * (f t * t^k)) gammaProbability :=
      (real_mem_l2_product_integrable hf2 (gamma_real_monomial_mem_l2 k)).const_mul _
    have hex : (fun t => f t * opLaguerre n t) =
        fun t => ∑ k ∈ Finset.range (n+1), opLaguerreCoefficient n k * (f t * t^k) := by
      funext t
      simp only [opLaguerre, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [hex, integral_finset_sum (Finset.range (n+1)) (fun k _ => hi k)] at he
    simp only [integral_mul_left, Finset.sum_range_succ] at he
    have hz : (∑ k ∈ Finset.range n, opLaguerreCoefficient n k *
        (∫ t : ℝ, f t * t^k ∂gammaProbability)) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [ih k (Finset.mem_range.mp hk), mul_zero]
    rw [hz, zero_add] at he
    exact (mul_eq_zero.mp he).resolve_left (opLaguerre_leading_coefficient_ne_zero n)

theorem laguerre_l2_inner_integral (n : ℕ) (g : LaguerreWeightedHilbert) :
    @inner ℂ LaguerreWeightedHilbert _ (laguerreL2Vector n) g =
      ∫ t : ℝ, (opLaguerre n t : ℂ) * g t ∂gammaProbability := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(op_laguerre_complex_mem_l2 n).coeFn_toLp] with t ht
  change (laguerreL2Vector n) t = _ at ht
  rw [ht]
  simp [RCLike.inner_apply, mul_comm]

theorem laguerre_l2_product_integrable (n : ℕ) (g : LaguerreWeightedHilbert) :
    Integrable (fun t : ℝ => (opLaguerre n t : ℂ) * g t) gammaProbability := by
  simpa only [Pi.smul_apply, smul_eq_mul] using
    memℒp_one_iff_integrable.mp ((Lp.memℒp g).smul (op_laguerre_complex_mem_l2 n)
      (by simp only [div_one, one_div, ENNReal.inv_two_add_inv_two] : (1 : ℝ≥0∞)/1 = 1/2+1/2))

/-- Completeness as an actual uniqueness statement in the gamma-weighted
complex Hilbert space, without an operator-domain hypothesis. -/
theorem laguerre_l2_eq_zero_of_orthogonal (g : LaguerreWeightedHilbert)
    (hg : ∀ n : ℕ, @inner ℂ LaguerreWeightedHilbert _ (laguerreL2Vector n) g = 0) :
    g = 0 := by
  have hgm : Measurable (fun t : ℝ => g t) := (Lp.stronglyMeasurable g).measurable
  have hrm : Measurable (fun t : ℝ => (g t).re) := Complex.continuous_re.measurable.comp hgm
  have him : Measurable (fun t : ℝ => (g t).im) := Complex.continuous_im.measurable.comp hgm
  have hr2 : Memℒp (fun t : ℝ => (g t).re) 2 gammaProbability :=
    (Lp.memℒp g).of_le hrm.aestronglyMeasurable
      (Eventually.of_forall fun t => by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_abs (g t))
  have hi2 : Memℒp (fun t : ℝ => (g t).im) 2 gammaProbability :=
    (Lp.memℒp g).of_le him.aestronglyMeasurable
      (Eventually.of_forall fun t => by simpa only [Real.norm_eq_abs] using Complex.abs_im_le_abs (g t))
  have hr : (fun t : ℝ => (g t).re) =ᵐ[gammaProbability] 0 := by
    apply gamma_real_l2_zero_of_laguerre _ hrm hr2
    intro n
    have hh := congrArg Complex.re (hg n)
    rw [laguerre_l2_inner_integral] at hh
    have hc := Complex.reCLM.integral_comp_comm (laguerre_l2_product_integrable n g)
    change (∫ t : ℝ, ((opLaguerre n t : ℂ) * g t).re ∂gammaProbability) =
      (∫ t : ℝ, (opLaguerre n t : ℂ) * g t ∂gammaProbability).re at hc
    rw [←hc] at hh
    simpa [Complex.mul_re, mul_comm] using hh
  have hi : (fun t : ℝ => (g t).im) =ᵐ[gammaProbability] 0 := by
    apply gamma_real_l2_zero_of_laguerre _ him hi2
    intro n
    have hh := congrArg Complex.im (hg n)
    rw [laguerre_l2_inner_integral] at hh
    have hc := Complex.imCLM.integral_comp_comm (laguerre_l2_product_integrable n g)
    change (∫ t : ℝ, ((opLaguerre n t : ℂ) * g t).im ∂gammaProbability) =
      (∫ t : ℝ, (opLaguerre n t : ℂ) * g t ∂gammaProbability).im at hc
    rw [←hc] at hh
    simpa [Complex.mul_im, mul_comm] using hh
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [hr,hi] with t htr hti
  exact Complex.ext htr hti

theorem normalized_laguerre_l2_eq_zero_of_orthogonal (g : LaguerreWeightedHilbert)
    (hg : ∀ n : ℕ, @inner ℂ LaguerreWeightedHilbert _ (normalizedLaguerreL2Vector n) g = 0) :
    g = 0 := by
  apply laguerre_l2_eq_zero_of_orthogonal g
  intro n
  have h := hg n
  simp only [normalizedLaguerreL2Vector, inner_smul_left, map_inv₀, Complex.conj_ofReal] at h
  exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero (by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by positivity : (0:ℝ)<n+1)))))

theorem normalized_laguerre_l2_orthogonal_eq_bot :
    (Submodule.span ℂ (Set.range normalizedLaguerreL2Vector))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro g hg
  rw [Submodule.mem_bot]
  apply normalized_laguerre_l2_eq_zero_of_orthogonal g
  intro n
  exact ((Submodule.mem_orthogonal _ g).mp hg) _
    (Submodule.subset_span (Set.mem_range_self n))

theorem normalized_laguerre_l2_dense_span :
    (Submodule.span ℂ (Set.range normalizedLaguerreL2Vector)).topologicalClosure = ⊤ :=
  Submodule.topologicalClosure_eq_top_iff.mpr normalized_laguerre_l2_orthogonal_eq_bot

/-- The complete marked Laguerre orthonormal basis of the actual weighted L². -/
def laguerreHilbertBasis : HilbertBasis ℕ ℂ LaguerreWeightedHilbert :=
  HilbertBasis.mkOfOrthogonalEqBot normalized_laguerre_l2_orthonormal
    normalized_laguerre_l2_orthogonal_eq_bot

theorem laguerre_hilbert_basis_apply (n : ℕ) :
    laguerreHilbertBasis n = normalizedLaguerreL2Vector n := by
  exact congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) n

end
end Sigma
