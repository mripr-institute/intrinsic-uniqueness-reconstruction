import SigmaOpGammaShapeThree
import SigmaOpDifferentialBridge
import SigmaOpGammaShapeThreeSpectral
import SigmaOpGammaShapeThreeEndpoints

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff ENNReal NNReal
set_option maxHeartbeats 800000

def gammaShapeThreeComplexExpression (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  -(t : ℂ) * deriv (deriv f) t - (3-(t : ℂ)) * deriv f t

theorem gamma_shape_three_complex_integral (f : ℝ → ℂ) :
    (∫ t, f t ∂gammaShapeThreeProbability) =
      ∫ t : ℝ in Ioi 0, ((t^2 * Real.exp (-t) / 2 : ℝ) : ℂ) * f t := by
  change (∫ t, f t ∂volume.withDensity
    (fun t => ((Real.toNNReal (gammaPDFReal 3 1 t) : ℝ≥0) : ℝ≥0∞))) = _
  rw [integral_withDensity_eq_integral_smul
    ((measurable_gammaPDFReal 3 1).real_toNNReal)]
  have hfun : (fun t => Real.toNNReal (gammaPDFReal 3 1 t) • f t) =
      (Ici (0 : ℝ)).indicator
        (fun t => ((t^2 * Real.exp (-t) / 2 : ℝ) : ℂ) * f t) := by
    funext t
    rw [NNReal.smul_def, Complex.real_smul,
      Real.coe_toNNReal _ (gammaPDFReal_nonneg (by norm_num) (by norm_num) t),
      gamma_shape_three_pdf]
    by_cases ht : 0 ≤ t <;> simp [ht]
  rw [hfun, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]

theorem gamma_shape_three_complex_stein (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) :
    (∫ t, (t : ℂ) * deriv f t + (3-(t : ℂ)) * f t
      ∂gammaShapeThreeProbability) = 0 := by
  rw [gamma_shape_three_complex_integral]
  have hc : ContDiff ℝ ∞ (fun t => (gammaShapeThreeFlux t : ℂ) * f t) :=
    (Complex.ofRealCLM.contDiff.comp gamma_shape_three_flux_contDiff).mul hf
  have hh := HasCompactSupport.integral_Ioi_deriv_eq
    (hc.of_le (by simp)) hs.mul_left (0 : ℝ)
  have he : (fun t => deriv (fun x => (gammaShapeThreeFlux x : ℂ) * f x) t) =
      fun t => ((t^2 * Real.exp (-t) / 2 : ℝ) : ℂ) *
        ((t : ℂ) * deriv f t + (3-(t : ℂ)) * f t) := by
    funext t
    have hd : HasDerivAt (fun x => (gammaShapeThreeFlux x : ℂ) * f x)
        (((3-t)*(t^2*Real.exp (-t)/2) : ℝ) * f t +
          (gammaShapeThreeFlux t : ℂ) * deriv f t) t := by
      simpa only [Function.comp_apply] using
        (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
      (gamma_shape_three_flux_hasDerivAt t)).mul
        ((hf.differentiable (by simp) t).hasDerivAt)
    rw [hd.deriv]
    simp only [gammaShapeThreeFlux, Complex.ofReal_mul, Complex.ofReal_sub,
      Complex.ofReal_pow, Complex.ofReal_ofNat, Complex.ofReal_div]
    ring
  rw [he] at hh
  simpa [gammaShapeThreeFlux] using hh

theorem gamma_shape_three_expression_contDiff (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (gammaShapeThreeComplexExpression f) := by
  have hd : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hdd : ContDiff ℝ ∞ (deriv (deriv f)) := (contDiff_infty_iff_deriv.mp hd).2
  exact ((Complex.ofRealCLM.contDiff.neg).mul hdd).sub
    ((contDiff_const.sub Complex.ofRealCLM.contDiff).mul hd)

theorem gamma_shape_three_expression_compact (f : ℝ → ℂ)
    (hs : HasCompactSupport f) : HasCompactSupport (gammaShapeThreeComplexExpression f) := by
  change HasCompactSupport (fun t : ℝ => -(t : ℂ)*deriv (deriv f) t +
    -((3-(t : ℂ))*deriv f t))
  exact hs.deriv.deriv.mul_left.add hs.deriv.mul_left.neg'

theorem gamma_shape_three_complex_green (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hs : HasCompactSupport f) :
    (∫ t, gammaShapeThreeComplexExpression f t * g t ∂gammaShapeThreeProbability) =
      ∫ t, f t * gammaShapeThreeComplexExpression g t ∂gammaShapeThreeProbability := by
  have hfd : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hgd : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.mp hg).2
  let w := fun t => deriv f t * g t - f t * deriv g t
  have hw : ContDiff ℝ ∞ w := (hfd.mul hg).sub (hf.mul hgd)
  have hws : HasCompactSupport w := by
    dsimp only [w]
    simp only [sub_eq_add_neg]
    exact hs.deriv.mul_right.add hs.mul_right.neg'
  have h := gamma_shape_three_complex_stein w hw hws
  have he : (fun t : ℝ => (t : ℂ) * deriv w t + (3-(t : ℂ)) * w t) =
      fun t => -(gammaShapeThreeComplexExpression f t * g t -
        f t * gammaShapeThreeComplexExpression g t) := by
    funext t
    dsimp only [w]
    rw [deriv_sub ((hfd.differentiable (by simp) t).mul (hg.differentiable (by simp) t))
      ((hf.differentiable (by simp) t).mul (hgd.differentiable (by simp) t)),
      deriv_mul (hfd.differentiable (by simp) t) (hg.differentiable (by simp) t),
      deriv_mul (hf.differentiable (by simp) t) (hgd.differentiable (by simp) t)]
    simp only [gammaShapeThreeComplexExpression]
    ring
  have hi : Integrable (fun t => gammaShapeThreeComplexExpression f t * g t)
      gammaShapeThreeProbability :=
    ((gamma_shape_three_expression_contDiff f hf).continuous.mul hg.continuous).integrable_of_hasCompactSupport
      (gamma_shape_three_expression_compact f hs).mul_right
  have hj : Integrable (fun t => f t * gammaShapeThreeComplexExpression g t)
      gammaShapeThreeProbability :=
    (hf.continuous.mul (gamma_shape_three_expression_contDiff g hg).continuous).integrable_of_hasCompactSupport
      hs.mul_right
  rw [he, integral_neg, integral_sub hi hj] at h
  exact sub_eq_zero.mp (neg_eq_zero.mp h)

theorem gamma_shape_three_laguerre_complex_contDiff (n : ℕ) :
    ContDiff ℝ ∞ (fun t : ℝ => (gammaShapeThreeLaguerre n t : ℂ)) := by
  apply Complex.ofRealCLM.contDiff.comp
  change ContDiff ℝ ∞ (fun t => (gammaShapeThreeLaguerrePolynomial n).eval t)
  have he : (fun t => (gammaShapeThreeLaguerrePolynomial n).eval t) =
      fun t => ∑ k ∈ (gammaShapeThreeLaguerrePolynomial n).support,
        (gammaShapeThreeLaguerrePolynomial n).coeff k * t^k := by
    funext t
    conv_lhs => rw [(gammaShapeThreeLaguerrePolynomial n).as_sum_support_C_mul_X_pow]
    simp [Polynomial.eval_finset_sum]
  rw [he]
  apply ContDiff.sum
  intro k _
  exact contDiff_const.mul (contDiff_id.pow k)

theorem gamma_shape_three_laguerre_complex_eigenvalue (n : ℕ) (t : ℝ) :
    gammaShapeThreeComplexExpression (fun u => (gammaShapeThreeLaguerre n u : ℂ)) t =
      (n : ℂ) * (gammaShapeThreeLaguerre n t : ℂ) := by
  have h := gamma_shape_three_laguerre_native_eigenvalue n t
  have hd : deriv (fun u => (gammaShapeThreeLaguerre n u : ℂ)) =
      fun u : ℝ => Complex.ofReal ((gammaShapeThreeLaguerrePolynomial n).derivative.eval u) := by
    funext u
    exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt u
      ((gammaShapeThreeLaguerrePolynomial n).hasDerivAt u)).deriv
  have hdd : deriv (deriv (fun u => (gammaShapeThreeLaguerre n u : ℂ))) t =
      Complex.ofReal ((gammaShapeThreeLaguerrePolynomial n).derivative.derivative.eval t) := by
    rw [hd]
    exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
      ((gammaShapeThreeLaguerrePolynomial n).derivative.hasDerivAt t)).deriv
  rw [gamma_shape_three_laguerre_second_derivative,
    gamma_shape_three_laguerre_derivative] at h
  dsimp [gammaShapeThreeComplexExpression]
  rw [hdd, hd]
  dsimp only at h ⊢
  exact_mod_cast h

theorem gamma_shape_three_test_moment (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (n : ℕ) :
    (∫ t, (gammaShapeThreeLaguerre n t : ℂ) * gammaShapeThreeComplexExpression f t
      ∂gammaShapeThreeProbability) =
      (n : ℂ) * ∫ t, (gammaShapeThreeLaguerre n t : ℂ) * f t
        ∂gammaShapeThreeProbability := by
  have h := gamma_shape_three_complex_green f
    (fun t => (gammaShapeThreeLaguerre n t : ℂ)) hf
    (gamma_shape_three_laguerre_complex_contDiff n) hs
  simp_rw [gamma_shape_three_laguerre_complex_eigenvalue] at h
  calc
    _ = ∫ t, gammaShapeThreeComplexExpression f t * (gammaShapeThreeLaguerre n t : ℂ)
        ∂gammaShapeThreeProbability := by congr 1; funext t; ring
    _ = ∫ t, f t * ((n : ℂ) * (gammaShapeThreeLaguerre n t : ℂ))
        ∂gammaShapeThreeProbability := h
    _ = ∫ t, (n : ℂ) * ((gammaShapeThreeLaguerre n t : ℂ) * f t)
        ∂gammaShapeThreeProbability := by congr 1; funext t; ring
    _ = _ := integral_mul_left _ _

def gammaShapeThreeCompactVector (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) : GammaShapeThreeWeightedHilbert :=
  (hf.continuous.memℒp_of_hasCompactSupport hs).toLp f

def gammaShapeThreeCompactImage (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) : GammaShapeThreeWeightedHilbert :=
  ((gamma_shape_three_expression_contDiff f hf).continuous.memℒp_of_hasCompactSupport
    (gamma_shape_three_expression_compact f hs)).toLp (gammaShapeThreeComplexExpression f)

theorem gamma_shape_three_compact_vector_coe (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) :
    (gammaShapeThreeCompactVector f hf hs : ℝ → ℂ) =ᵐ[gammaShapeThreeProbability] f :=
  Memℒp.coeFn_toLp _

theorem gamma_shape_three_compact_image_coe (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) :
    (gammaShapeThreeCompactImage f hf hs : ℝ → ℂ) =ᵐ[gammaShapeThreeProbability]
      gammaShapeThreeComplexExpression f := Memℒp.coeFn_toLp _

theorem gamma_shape_three_compact_image_raw_coefficient (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (n : ℕ) :
    @inner ℂ GammaShapeThreeWeightedHilbert _ (gammaShapeThreeL2Vector n)
        (gammaShapeThreeCompactImage f hf hs) =
      (n : ℂ) * @inner ℂ GammaShapeThreeWeightedHilbert _ (gammaShapeThreeL2Vector n)
        (gammaShapeThreeCompactVector f hf hs) := by
  rw [gamma_shape_three_l2_inner_integral, gamma_shape_three_l2_inner_integral]
  have h1 : (∫ t, (gammaShapeThreeLaguerre n t : ℂ) * gammaShapeThreeCompactImage f hf hs t
      ∂gammaShapeThreeProbability) =
      ∫ t, (gammaShapeThreeLaguerre n t : ℂ) * gammaShapeThreeComplexExpression f t
        ∂gammaShapeThreeProbability := by
    apply integral_congr_ae
    filter_upwards [gamma_shape_three_compact_image_coe f hf hs] with t ht
    rw [ht]
  have h2 : (∫ t, (gammaShapeThreeLaguerre n t : ℂ) * gammaShapeThreeCompactVector f hf hs t
      ∂gammaShapeThreeProbability) =
      ∫ t, (gammaShapeThreeLaguerre n t : ℂ) * f t ∂gammaShapeThreeProbability := by
    apply integral_congr_ae
    filter_upwards [gamma_shape_three_compact_vector_coe f hf hs] with t ht
    rw [ht]
  rw [h1, h2, gamma_shape_three_test_moment f hf hs n]

theorem gamma_shape_three_compact_image_coefficient (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (n : ℕ) :
    gammaShapeThreeHilbertBasis.repr (gammaShapeThreeCompactImage f hf hs) n =
      (n : ℂ) * gammaShapeThreeHilbertBasis.repr (gammaShapeThreeCompactVector f hf hs) n := by
  simp only [gammaShapeThreeHilbertBasis.repr_apply_apply,
    gamma_shape_three_hilbert_basis_apply, normalizedGammaShapeThreeL2Vector, inner_smul_left]
  rw [gamma_shape_three_compact_image_raw_coefficient]
  ring

theorem gamma_shape_three_compact_mem_spectral_domain (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    gammaShapeThreeCompactVector f hf hs ∈ gammaShapeThreeSpectralOperator.domain := by
  change Memℓp (fun n : ℕ => (n : ℂ) *
    gammaShapeThreeHilbertBasis.repr (gammaShapeThreeCompactVector f hf hs) n) 2
  have he : (fun n : ℕ => (n : ℂ) *
      gammaShapeThreeHilbertBasis.repr (gammaShapeThreeCompactVector f hf hs) n) =
      fun n => gammaShapeThreeHilbertBasis.repr (gammaShapeThreeCompactImage f hf hs) n := by
    funext n
    exact (gamma_shape_three_compact_image_coefficient f hf hs n).symm
  rw [he]
  exact (gammaShapeThreeHilbertBasis.repr (gammaShapeThreeCompactImage f hf hs)).property

theorem gamma_shape_three_spectral_test_action (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    gammaShapeThreeSpectralOperator ⟨gammaShapeThreeCompactVector f hf hs,
      gamma_shape_three_compact_mem_spectral_domain f hf hs⟩ =
        gammaShapeThreeCompactImage f hf hs := by
  apply gammaShapeThreeHilbertBasis.repr.injective
  apply lp.ext
  funext n
  rw [gamma_shape_three_spectral_coordinate, gamma_shape_three_compact_image_coefficient]

def gammaShapeThreeCompactTestDomain : Submodule ℂ GammaShapeThreeWeightedHilbert where
  carrier := {x | ∃ f : ℝ → ℂ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    tsupport f ⊆ Ioi 0 ∧ (x : ℝ → ℂ) =ᵐ[gammaShapeThreeProbability] f}
  zero_mem' := by
    refine ⟨fun _ => 0, contDiff_const, HasCompactSupport.zero, ?_,
      Lp.coeFn_zero ℂ 2 gammaShapeThreeProbability⟩
    simp [tsupport, Function.support]
  add_mem' := by
    rintro x y ⟨f,hf,hfs,hfp,hfx⟩ ⟨g,hg,hgs,hgp,hgy⟩
    refine ⟨fun t => f t+g t, hf.add hg, hfs.add hgs, ?_, ?_⟩
    · exact tsupport_add.trans (union_subset hfp hgp)
    · filter_upwards [Lp.coeFn_add x y, hfx, hgy] with t ht hx hy
      simpa only [Pi.add_apply, hx, hy] using ht
  smul_mem' := by
    rintro c x ⟨f,hf,hfs,hfp,hfx⟩
    refine ⟨fun t => c * f t, contDiff_const.mul hf, hfs.mul_left, ?_, ?_⟩
    · exact tsupport_mul_subset_right.trans hfp
    · filter_upwards [Lp.coeFn_smul c x, hfx] with t ht hx
      simpa only [Pi.smul_apply, smul_eq_mul, hx] using ht

theorem gamma_shape_three_compact_vector_eq_of_ae (x : GammaShapeThreeWeightedHilbert)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f)
    (hx : (x : ℝ → ℂ) =ᵐ[gammaShapeThreeProbability] f) :
    gammaShapeThreeCompactVector f hf hs = x := by
  apply Lp.ext
  exact (gamma_shape_three_compact_vector_coe f hf hs).trans hx.symm

theorem gamma_shape_three_compact_test_domain_le_spectral :
    gammaShapeThreeCompactTestDomain ≤ gammaShapeThreeSpectralOperator.domain := by
  rintro x ⟨f,hf,hs,_,hx⟩
  rw [← gamma_shape_three_compact_vector_eq_of_ae x f hf hs hx]
  exact gamma_shape_three_compact_mem_spectral_domain f hf hs

/-- The literal compact-interior differential operator. Spectral membership
is derived above rather than imposed on its test domain. -/
def gammaShapeThreeMinimalOperator :
    GammaShapeThreeWeightedHilbert →ₗ.[ℂ] GammaShapeThreeWeightedHilbert :=
  gammaShapeThreeSpectralOperator.domRestrict gammaShapeThreeCompactTestDomain

theorem gamma_shape_three_minimal_domain :
    gammaShapeThreeMinimalOperator.domain = gammaShapeThreeCompactTestDomain :=
  inf_eq_left.mpr gamma_shape_three_compact_test_domain_le_spectral

theorem gamma_shape_three_minimal_le_spectral :
    gammaShapeThreeMinimalOperator ≤ gammaShapeThreeSpectralOperator := LinearPMap.domRestrict_le

theorem gamma_shape_three_compact_test_mem (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (hpos : tsupport f ⊆ Ioi 0) :
    gammaShapeThreeCompactVector f hf hs ∈ gammaShapeThreeMinimalOperator.domain := by
  rw [gamma_shape_three_minimal_domain]
  exact ⟨f,hf,hs,hpos,gamma_shape_three_compact_vector_coe f hf hs⟩

theorem gamma_shape_three_minimal_test_action (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (hpos : tsupport f ⊆ Ioi 0) :
    gammaShapeThreeMinimalOperator ⟨gammaShapeThreeCompactVector f hf hs,
      gamma_shape_three_compact_test_mem f hf hs hpos⟩ = gammaShapeThreeCompactImage f hf hs := by
  exact (gamma_shape_three_minimal_le_spectral.2 (y :=
    ⟨gammaShapeThreeCompactVector f hf hs,
      gamma_shape_three_compact_mem_spectral_domain f hf hs⟩) rfl).trans
        (gamma_shape_three_spectral_test_action f hf hs)

end
end Sigma
