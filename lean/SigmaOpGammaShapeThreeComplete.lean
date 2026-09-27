import SigmaOpGammaShapeThree
import SigmaOpLaguerreMomentDensity
import Mathlib.Analysis.InnerProductSpace.l2Space

namespace Sigma
noncomputable section
open MeasureTheory Filter Polynomial
open scoped Topology ENNReal BigOperators

theorem gamma_shape_three_real_monomial_mem_l2 (n : ℕ) :
    Memℒp (fun t : ℝ => t^n) 2 gammaShapeThreeProbability := by
  apply (memℒp_two_iff_integrable_sq (by fun_prop)).mpr
  simpa only [←pow_mul] using gamma_shape_three_monomial_integrable (n*2)

/-- A genuine small exponential moment of the actual shape-three law. -/
theorem gamma_shape_three_small_exponential_integral :
    (∫ t : ℝ, Real.exp ((1/2)*|t|) ∂gammaShapeThreeProbability) = 8 := by
  rw [gamma_shape_three_integral]
  have hi := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := 3) (r := 1/2) (by norm_num) (by norm_num)
  norm_num [Real.Gamma_nat_eq_factorial, Real.rpow_two, Real.rpow_natCast] at hi
  calc
    (∫ t : ℝ in Set.Ioi 0, (t^2 * Real.exp (-t) / 2) * Real.exp ((1/2)*|t|)) =
        (∫ t : ℝ in Set.Ioi 0, t^2 * Real.exp (-(1/2*t))) / 2 := by
      rw [←integral_div]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [abs_of_pos ht, div_mul_eq_mul_div, mul_assoc, ←Real.exp_add]
      rw [show -t + (1/2)*t = -((1/2)*t) by ring]
    _ = 8 := by rw [hi]; norm_num

theorem gamma_shape_three_small_exponential_mem_l2 :
    Memℒp (fun t : ℝ => Real.exp ((1/4)*|t|)) 2 gammaShapeThreeProbability := by
  have hi : Integrable (fun t : ℝ => Real.exp ((1/2)*|t|)) gammaShapeThreeProbability := by
    by_contra h
    have he := gamma_shape_three_small_exponential_integral
    rw [integral_undef h] at he
    norm_num at he
  apply (memℒp_two_iff_integrable_sq
    ((continuous_const.mul continuous_id.abs).rexp.aestronglyMeasurable)).mpr
  convert hi using 1
  funext t
  rw [pow_two, ←Real.exp_add]
  congr 1
  simp only [id_eq]
  ring

theorem gamma_shape_three_real_l2_zero_of_laguerre (f : ℝ → ℝ)
    (hf : Measurable f) (hf2 : Memℒp f 2 gammaShapeThreeProbability)
    (hL : ∀ n : ℕ, (∫ t : ℝ, f t * gammaShapeThreeLaguerre n t
      ∂gammaShapeThreeProbability) = 0) : f =ᵐ[gammaShapeThreeProbability] 0 := by
  apply real_mem_l2_zero_of_moments gammaShapeThreeProbability f hf hf2
    gamma_shape_three_real_monomial_mem_l2 (1/4) (by norm_num)
    gamma_shape_three_small_exponential_mem_l2
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have he := hL n
    have hi (k : ℕ) : Integrable (fun t : ℝ =>
        (gammaShapeThreeLaguerrePolynomial n).coeff k * (f t * t^k))
          gammaShapeThreeProbability :=
      (real_mem_l2_product_integrable hf2
        (gamma_shape_three_real_monomial_mem_l2 k)).const_mul _
    have hex : (fun t => f t * gammaShapeThreeLaguerre n t) =
        fun t => ∑ k ∈ Finset.range (n+1),
          (gammaShapeThreeLaguerrePolynomial n).coeff k * (f t * t^k) := by
      funext t
      unfold gammaShapeThreeLaguerre
      rw [eval_eq_sum_range' (by
        have := gamma_shape_three_laguerre_degree_le n
        omega : (gammaShapeThreeLaguerrePolynomial n).natDegree < n+1),
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [hex, integral_finset_sum (Finset.range (n+1)) (fun k _ => hi k)] at he
    simp only [integral_mul_left, Finset.sum_range_succ] at he
    have hz : (∑ k ∈ Finset.range n, (gammaShapeThreeLaguerrePolynomial n).coeff k *
        (∫ t : ℝ, f t * t^k ∂gammaShapeThreeProbability)) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [ih k (Finset.mem_range.mp hk), mul_zero]
    rw [hz, zero_add] at he
    exact (mul_eq_zero.mp he).resolve_left (gamma_shape_three_laguerre_leading_ne_zero n)

theorem gamma_shape_three_l2_inner_integral (n : ℕ) (g : GammaShapeThreeWeightedHilbert) :
    @inner ℂ GammaShapeThreeWeightedHilbert _ (gammaShapeThreeL2Vector n) g =
      ∫ t : ℝ, (gammaShapeThreeLaguerre n t : ℂ) * g t ∂gammaShapeThreeProbability := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(gamma_shape_three_complex_polynomial_mem_l2
    (gammaShapeThreeLaguerrePolynomial n)).coeFn_toLp] with t ht
  change (gammaShapeThreeL2Vector n) t = _ at ht
  rw [ht]
  simp [RCLike.inner_apply, mul_comm, gammaShapeThreeLaguerre]

theorem gamma_shape_three_l2_product_integrable (n : ℕ) (g : GammaShapeThreeWeightedHilbert) :
    Integrable (fun t : ℝ => (gammaShapeThreeLaguerre n t : ℂ) * g t)
      gammaShapeThreeProbability := by
  simpa only [Pi.smul_apply, smul_eq_mul, gammaShapeThreeLaguerre] using
    memℒp_one_iff_integrable.mp ((Lp.memℒp g).smul
      (gamma_shape_three_complex_polynomial_mem_l2 (gammaShapeThreeLaguerrePolynomial n))
      (by simp only [div_one, one_div, ENNReal.inv_two_add_inv_two] : (1 : ℝ≥0∞)/1 = 1/2+1/2))

theorem gamma_shape_three_l2_eq_zero_of_orthogonal (g : GammaShapeThreeWeightedHilbert)
    (hg : ∀ n : ℕ, @inner ℂ GammaShapeThreeWeightedHilbert _ (gammaShapeThreeL2Vector n) g = 0) :
    g = 0 := by
  have hgm : Measurable (fun t : ℝ => g t) := (Lp.stronglyMeasurable g).measurable
  have hrm : Measurable (fun t : ℝ => (g t).re) := Complex.continuous_re.measurable.comp hgm
  have him : Measurable (fun t : ℝ => (g t).im) := Complex.continuous_im.measurable.comp hgm
  have hr2 : Memℒp (fun t : ℝ => (g t).re) 2 gammaShapeThreeProbability :=
    (Lp.memℒp g).of_le hrm.aestronglyMeasurable
      (Eventually.of_forall fun t => by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_abs (g t))
  have hi2 : Memℒp (fun t : ℝ => (g t).im) 2 gammaShapeThreeProbability :=
    (Lp.memℒp g).of_le him.aestronglyMeasurable
      (Eventually.of_forall fun t => by simpa only [Real.norm_eq_abs] using Complex.abs_im_le_abs (g t))
  have hr : (fun t : ℝ => (g t).re) =ᵐ[gammaShapeThreeProbability] 0 := by
    apply gamma_shape_three_real_l2_zero_of_laguerre _ hrm hr2
    intro n
    have hh := congrArg Complex.re (hg n)
    rw [gamma_shape_three_l2_inner_integral] at hh
    have hc := Complex.reCLM.integral_comp_comm (gamma_shape_three_l2_product_integrable n g)
    change (∫ t : ℝ, ((gammaShapeThreeLaguerre n t : ℂ) * g t).re
      ∂gammaShapeThreeProbability) =
      (∫ t : ℝ, (gammaShapeThreeLaguerre n t : ℂ) * g t ∂gammaShapeThreeProbability).re at hc
    rw [←hc] at hh
    simpa [Complex.mul_re, mul_comm] using hh
  have hi : (fun t : ℝ => (g t).im) =ᵐ[gammaShapeThreeProbability] 0 := by
    apply gamma_shape_three_real_l2_zero_of_laguerre _ him hi2
    intro n
    have hh := congrArg Complex.im (hg n)
    rw [gamma_shape_three_l2_inner_integral] at hh
    have hc := Complex.imCLM.integral_comp_comm (gamma_shape_three_l2_product_integrable n g)
    change (∫ t : ℝ, ((gammaShapeThreeLaguerre n t : ℂ) * g t).im
      ∂gammaShapeThreeProbability) =
      (∫ t : ℝ, (gammaShapeThreeLaguerre n t : ℂ) * g t ∂gammaShapeThreeProbability).im at hc
    rw [←hc] at hh
    simpa [Complex.mul_im, mul_comm] using hh
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [hr,hi] with t htr hti
  exact Complex.ext htr hti

theorem normalized_gamma_shape_three_l2_orthogonal_eq_bot :
    (Submodule.span ℂ (Set.range normalizedGammaShapeThreeL2Vector))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro g hg
  rw [Submodule.mem_bot]
  apply gamma_shape_three_l2_eq_zero_of_orthogonal g
  intro n
  have h := ((Submodule.mem_orthogonal _ g).mp hg) _
    (Submodule.subset_span (Set.mem_range_self n))
  simp only [normalizedGammaShapeThreeL2Vector, inner_smul_left, map_inv₀,
    Complex.conj_ofReal] at h
  exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero (by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2
      (by positivity : (0:ℝ)<(n+1 : ℝ)*(n+2)/2)))))

/-- The complete normalized Laguerre basis in the actual shape-three weighted L² space. -/
def gammaShapeThreeHilbertBasis : HilbertBasis ℕ ℂ GammaShapeThreeWeightedHilbert :=
  HilbertBasis.mkOfOrthogonalEqBot normalized_gamma_shape_three_l2_orthonormal
    normalized_gamma_shape_three_l2_orthogonal_eq_bot

theorem gamma_shape_three_hilbert_basis_apply (n : ℕ) :
    gammaShapeThreeHilbertBasis n = normalizedGammaShapeThreeL2Vector n := by
  exact congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) n

theorem gamma_shape_three_basis_zero_coe :
    (gammaShapeThreeHilbertBasis 0 : ℝ → ℂ) =ᵐ[gammaShapeThreeProbability] fun _ => 1 := by
  rw [gamma_shape_three_hilbert_basis_apply, normalizedGammaShapeThreeL2Vector]
  norm_num only [Nat.cast_zero, zero_add, one_mul, div_self (by norm_num : (2:ℝ)≠0),
    Real.sqrt_one, Complex.ofReal_one, inv_one, one_smul]
  filter_upwards [(gamma_shape_three_complex_polynomial_mem_l2
    (gammaShapeThreeLaguerrePolynomial 0)).coeFn_toLp] with t ht
  change gammaShapeThreeL2Vector 0 t = _ at ht
  simpa [gammaShapeThreeLaguerre, gamma_shape_three_laguerre_zero] using ht

end
end Sigma
