import SigmaOpLaguerreSpectral
import SigmaStein

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff ENNReal NNReal

theorem gamma_complex_stein (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) :
    (∫ t : ℝ, (t : ℂ) * deriv f t + (2-(t : ℂ)) * f t ∂gammaProbability) = 0 := by
  rw [gamma_probability_complex_integral]
  have hc : ContDiff ℝ ∞ (fun t => (steinFlux t : ℂ) * f t) :=
    (Complex.ofRealCLM.contDiff.comp steinFlux_contDiff).mul hf
  have hh := HasCompactSupport.integral_Ioi_deriv_eq
    (hc.of_le (by simp)) hs.mul_left (0 : ℝ)
  have he : (fun t => deriv (fun x => (steinFlux x : ℂ) * f x) t) =
      (fun t => (SigmaPresentations.density t : ℂ) *
        ((t : ℂ) * deriv f t + (2-(t : ℂ)) * f t)) := by
    funext t
    have hd : HasDerivAt (fun x => (steinFlux x : ℂ) * f x)
        (((2-t)*SigmaPresentations.density t : ℝ) * f t +
          (steinFlux t : ℂ) * deriv f t) t := by
      simpa only [Function.comp_apply] using
        (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (steinFlux_hasDerivAt t)).mul
          ((hf.differentiable (by simp) t).hasDerivAt)
    rw [hd.deriv]
    simp only [steinFlux, SigmaPresentations.density, Complex.ofReal_mul,
      Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_ofNat]
    ring
  rw [he] at hh
  simpa [steinFlux] using hh

theorem op_complex_laguerre_expression_contDiff (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (opComplexLaguerreExpression f) := by
  have hd : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hdd : ContDiff ℝ ∞ (deriv (deriv f)) := (contDiff_infty_iff_deriv.mp hd).2
  exact ((Complex.ofRealCLM.contDiff.neg).mul hdd).sub
    ((contDiff_const.sub Complex.ofRealCLM.contDiff).mul hd)

theorem op_complex_laguerre_expression_compact (f : ℝ → ℂ) (hs : HasCompactSupport f) :
    HasCompactSupport (opComplexLaguerreExpression f) :=
  by
    change HasCompactSupport (fun t : ℝ => -(t : ℂ)*deriv (deriv f) t +
      -((2-(t : ℂ))*deriv f t))
    exact hs.deriv.deriv.mul_left.add hs.deriv.mul_left.neg'

set_option maxHeartbeats 800000 in
/-- Green symmetry with the literal differential expression and a compact
test, before any self-adjoint domain is imposed. The second function need not
be compactly supported, so this applies to the marked Laguerre polynomials. -/
theorem op_complex_laguerre_green_identity (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hs : HasCompactSupport f) :
    (∫ t, opComplexLaguerreExpression f t * g t ∂gammaProbability) =
      ∫ t, f t * opComplexLaguerreExpression g t ∂gammaProbability := by
  have hfd : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hgd : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.mp hg).2
  let w := fun t => deriv f t * g t - f t * deriv g t
  have hw : ContDiff ℝ ∞ w := (hfd.mul hg).sub (hf.mul hgd)
  have hws : HasCompactSupport w := by
    dsimp only [w]
    simp only [sub_eq_add_neg]
    exact hs.deriv.mul_right.add hs.mul_right.neg'
  have h := gamma_complex_stein w hw hws
  have he : (fun t : ℝ => (t : ℂ) * deriv w t + (2-(t : ℂ)) * w t) =
      fun t => -(opComplexLaguerreExpression f t * g t -
        f t * opComplexLaguerreExpression g t) := by
    funext t
    dsimp only [w]
    rw [deriv_sub ((hfd.differentiable (by simp) t).mul (hg.differentiable (by simp) t))
      ((hf.differentiable (by simp) t).mul (hgd.differentiable (by simp) t)),
      deriv_mul (hfd.differentiable (by simp) t) (hg.differentiable (by simp) t),
      deriv_mul (hf.differentiable (by simp) t) (hgd.differentiable (by simp) t)]
    simp only [opComplexLaguerreExpression]
    ring
  have hi : Integrable (fun t => opComplexLaguerreExpression f t * g t) gammaProbability :=
    ((op_complex_laguerre_expression_contDiff f hf).continuous.mul hg.continuous).integrable_of_hasCompactSupport
      (op_complex_laguerre_expression_compact f hs).mul_right
  have hj : Integrable (fun t => f t * opComplexLaguerreExpression g t) gammaProbability :=
    (hf.continuous.mul (op_complex_laguerre_expression_contDiff g hg).continuous).integrable_of_hasCompactSupport
      hs.mul_right
  rw [he, integral_neg, integral_sub hi hj] at h
  exact sub_eq_zero.mp (neg_eq_zero.mp h)

theorem op_laguerre_complex_contDiff (n : ℕ) :
    ContDiff ℝ ∞ (fun t : ℝ => (opLaguerre n t : ℂ)) := by
  have hr : ContDiff ℝ ∞ (opLaguerre n) := by
    unfold opLaguerre
    apply ContDiff.sum
    intro k _
    exact contDiff_const.mul (contDiff_id.pow k)
  exact Complex.ofRealCLM.contDiff.comp hr

theorem op_complex_laguerre_test_moment (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (n : ℕ) :
    (∫ t, (opLaguerre n t : ℂ) * opComplexLaguerreExpression f t ∂gammaProbability) =
      (n : ℂ) * ∫ t, (opLaguerre n t : ℂ) * f t ∂gammaProbability := by
  have h := op_complex_laguerre_green_identity f (fun t => (opLaguerre n t : ℂ))
    hf (op_laguerre_complex_contDiff n) hs
  simp_rw [op_laguerre_native_complex_eigenvalue] at h
  calc
    _ = ∫ t, opComplexLaguerreExpression f t * (opLaguerre n t : ℂ) ∂gammaProbability := by
      congr 1; funext t; ring
    _ = ∫ t, f t * ((n : ℂ) * (opLaguerre n t : ℂ)) ∂gammaProbability := h
    _ = ∫ t, (n : ℂ) * ((opLaguerre n t : ℂ) * f t) ∂gammaProbability := by
      congr 1; funext t; ring
    _ = _ := integral_mul_left _ _

def smoothCompactL2Vector (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) : LaguerreWeightedHilbert :=
  (hf.continuous.memℒp_of_hasCompactSupport hs).toLp f

def smoothCompactL2Image (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) : LaguerreWeightedHilbert :=
  ((op_complex_laguerre_expression_contDiff f hf).continuous.memℒp_of_hasCompactSupport
    (op_complex_laguerre_expression_compact f hs)).toLp (opComplexLaguerreExpression f)

theorem smooth_compact_l2_coe (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) :
    (smoothCompactL2Vector f hf hs : ℝ → ℂ) =ᵐ[gammaProbability] f :=
  Memℒp.coeFn_toLp _

theorem smooth_compact_image_coe (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) :
    (smoothCompactL2Image f hf hs : ℝ → ℂ) =ᵐ[gammaProbability] opComplexLaguerreExpression f :=
  Memℒp.coeFn_toLp _

theorem smooth_compact_image_raw_coefficient (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (n : ℕ) :
    @inner ℂ LaguerreWeightedHilbert _ (laguerreL2Vector n) (smoothCompactL2Image f hf hs) =
      (n : ℂ) * @inner ℂ LaguerreWeightedHilbert _ (laguerreL2Vector n) (smoothCompactL2Vector f hf hs) := by
  rw [laguerre_l2_inner_integral, laguerre_l2_inner_integral]
  have h1 : (∫ t, (opLaguerre n t : ℂ) * smoothCompactL2Image f hf hs t ∂gammaProbability) =
      ∫ t, (opLaguerre n t : ℂ) * opComplexLaguerreExpression f t ∂gammaProbability := by
    apply integral_congr_ae
    filter_upwards [smooth_compact_image_coe f hf hs] with t ht
    rw [ht]
  have h2 : (∫ t, (opLaguerre n t : ℂ) * smoothCompactL2Vector f hf hs t ∂gammaProbability) =
      ∫ t, (opLaguerre n t : ℂ) * f t ∂gammaProbability := by
    apply integral_congr_ae
    filter_upwards [smooth_compact_l2_coe f hf hs] with t ht
    rw [ht]
  rw [h1, h2, op_complex_laguerre_test_moment f hf hs n]

theorem smooth_compact_image_coefficient (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (n : ℕ) :
    laguerreHilbertBasis.repr (smoothCompactL2Image f hf hs) n =
      (n : ℂ) * laguerreHilbertBasis.repr (smoothCompactL2Vector f hf hs) n := by
  simp only [laguerreHilbertBasis.repr_apply_apply, laguerre_hilbert_basis_apply,
    normalizedLaguerreL2Vector, inner_smul_left]
  rw [smooth_compact_image_raw_coefficient]
  ring

/-- Domain membership is derived from actual derivatives and integration by
parts: the differential image's square-summable coefficients are n times the
test's coefficients. It is not an assumption on a test-function structure. -/
theorem smooth_compact_mem_laguerre_domain (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) :
    smoothCompactL2Vector f hf hs ∈ (laguerreSpectralOperator id).domain := by
  change Memℓp (fun n : ℕ => (n : ℂ) * laguerreHilbertBasis.repr (smoothCompactL2Vector f hf hs) n) 2
  have he : (fun n : ℕ => (n : ℂ) * laguerreHilbertBasis.repr (smoothCompactL2Vector f hf hs) n) =
      fun n => laguerreHilbertBasis.repr (smoothCompactL2Image f hf hs) n := by
    funext n
    exact (smooth_compact_image_coefficient f hf hs n).symm
  rw [he]
  exact (laguerreHilbertBasis.repr (smoothCompactL2Image f hf hs)).property

/-- The constructed spectral operator agrees with the paper's literal
differential expression on every smooth compact test. This is an extension
statement, not yet equality with the compact-interior graph closure. -/
theorem laguerre_spectral_extends_differential_test (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) :
    laguerreSpectralOperator id ⟨smoothCompactL2Vector f hf hs,
      smooth_compact_mem_laguerre_domain f hf hs⟩ = smoothCompactL2Image f hf hs := by
  apply laguerreHilbertBasis.repr.injective
  apply lp.ext
  funext n
  rw [laguerre_spectral_coordinate, smooth_compact_image_coefficient]
  rfl

end
end Sigma
