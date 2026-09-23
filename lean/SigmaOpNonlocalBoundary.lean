import SigmaOpLaguerreSpectral

namespace Sigma
noncomputable section
open MeasureTheory Set Filter

def swappedLaguerreMultiplier (x : ℝ) : ℝ := if x=3 then 4 else if x=4 then 3 else x

theorem swapped_laguerre_first_three (n : ℕ) (hn : n ≤ 2) :
    swappedLaguerreMultiplier n = n := by
  interval_cases n <;> norm_num [swappedLaguerreMultiplier]

/-- A local coefficient expression must represent every polynomial in the
operator domain. Equalities are of actual weighted-L² representatives. -/
def HasLaguerreLocalExpression
    (S : LaguerreWeightedHilbert →ₗ.[ℂ] LaguerreWeightedHilbert) (a b : ℝ → ℝ) : Prop :=
  ∀ n : ℕ, ∃ hn : laguerreL2Vector n ∈ S.domain,
    (fun t : ℝ => (S ⟨laguerreL2Vector n, hn⟩) t) =ᵐ[gammaProbability]
      (fun t => (opExpression a b (opLaguerre n) t : ℂ))

theorem swapped_laguerre_no_scalar_local_expression (a b : ℝ → ℝ) :
    ¬ (∀ n : ℕ, (fun t => opExpression a b (opLaguerre n) t) =ᵐ[gammaProbability]
      (fun t => swappedLaguerreMultiplier n * opLaguerre n t)) := by
  intro h
  have he1 : opLaguerre 1 = opLinearProbe := by
    funext t
    exact (opLaguerre_first_three t).2.1
  have he2 : opLaguerre 2 = opQuadraticProbe := by
    funext t
    exact (opLaguerre_first_three t).2.2
  have h1 : ∀ᵐ t ∂gammaProbability, opExpression a b opLinearProbe t = 2-t := by
    filter_upwards [h 1] with t ht
    simpa [he1, swappedLaguerreMultiplier, opLinearProbe,
      SigmaPresentations.linearEigenfunction] using ht
  have h2 : ∀ᵐ t ∂gammaProbability, opExpression a b opQuadraticProbe t = t^2-6*t+6 := by
    filter_upwards [h 2] with t ht
    rw [he2] at ht
    norm_num [swappedLaguerreMultiplier] at ht
    change opExpression a b opQuadraticProbe t = 2*(t^2/2-3*t+3) at ht
    linarith
  have hcoeff := (operator_two_probe_ae_iff gammaProbability a b).mp ⟨h1,h2⟩
  have hzero : ∀ᵐ t ∂gammaProbability, opLaguerre 3 t = 0 := by
    filter_upwards [hcoeff, h 3] with t ht h3
    have he : opExpression a b (opLaguerre 3) t =
        opExpression id (fun x => 2-x) (opLaguerre 3) t := by
      simp only [opExpression, SigmaPresentations.differentialExpression,
        SigmaPresentations.localExpression]
      rw [ht.1,ht.2]
      rfl
    rw [he, op_laguerre_expression_eigenvalue] at h3
    norm_num [swappedLaguerreMultiplier] at h3
    linarith
  have hnz : opLaguerrePolynomial 3 ≠ 0 := by
    intro he
    have hc := congrArg (fun P : Polynomial ℝ => P.coeff 3) he
    change (opLaguerrePolynomial 3).coeff 3 = (0 : Polynomial ℝ).coeff 3 at hc
    rw [op_laguerre_polynomial_coeff, Polynomial.coeff_zero] at hc
    exact opLaguerre_leading_coefficient_ne_zero 3 hc
  have hne := gamma_polynomial_nonzero_ae (opLaguerrePolynomial 3) hnz
  obtain ⟨t,ht,hn⟩ := (hzero.and hne).exists
  exact hn (by simpa only [op_laguerre_polynomial_eval] using ht)

theorem swapped_laguerre_no_local_expression :
    ¬ ∃ a b : ℝ → ℝ, HasLaguerreLocalExpression (laguerreSpectralOperator swappedLaguerreMultiplier) a b := by
  rintro ⟨a,b,h⟩
  apply swapped_laguerre_no_scalar_local_expression a b
  intro n
  obtain ⟨hn,hh⟩ := h n
  have hout := laguerre_spectral_raw_representative swappedLaguerreMultiplier n
  filter_upwards [hh,hout] with t ht hu
  apply Complex.ofReal_injective
  exact ht.symm.trans hu

theorem laguerre_swapped_operator_distinct :
    laguerreSpectralOperator id ≠ laguerreSpectralOperator swappedLaguerreMultiplier := by
  intro h
  have hx : laguerreSpectralOperator id
      ⟨laguerreL2Vector 3, laguerre_raw_mem_spectral_domain id 3⟩ =
      laguerreSpectralOperator swappedLaguerreMultiplier
      ⟨laguerreL2Vector 3, laguerre_raw_mem_spectral_domain swappedLaguerreMultiplier 3⟩ := by
    exact (le_of_eq h).2 rfl
  rw [laguerre_spectral_raw_action,laguerre_spectral_raw_action] at hx
  norm_num [swappedLaguerreMultiplier] at hx
  have hz : (1 : ℂ) • laguerreL2Vector 3 = 0 := by
    have hh := sub_eq_zero.mpr hx
    rw [←sub_smul] at hh
    norm_num at hh
    simpa using hh
  exact laguerre_l2_vector_ne_zero 3 (by simpa using hz)

/-- Genuine self-adjoint operators on the actual weighted complex Hilbert
space agree on the constant and both probe polynomials yet are different;
the swapped operator cannot be a local second-order expression even a.e. -/
theorem actual_selfadjoint_probe_nonidentification :
    IsSelfAdjoint (laguerreSpectralOperator id) ∧
    IsSelfAdjoint (laguerreSpectralOperator swappedLaguerreMultiplier) ∧
    laguerreSpectralOperator id ≠ laguerreSpectralOperator swappedLaguerreMultiplier ∧
    (∀ n : ℕ, n ≤ 2 →
      laguerreSpectralOperator id ⟨laguerreL2Vector n, laguerre_raw_mem_spectral_domain id n⟩ =
      laguerreSpectralOperator swappedLaguerreMultiplier
        ⟨laguerreL2Vector n, laguerre_raw_mem_spectral_domain swappedLaguerreMultiplier n⟩) ∧
    ¬ ∃ a b : ℝ → ℝ, HasLaguerreLocalExpression (laguerreSpectralOperator swappedLaguerreMultiplier) a b := by
  refine ⟨laguerre_spectral_selfAdjoint id, laguerre_spectral_selfAdjoint _,
    laguerre_swapped_operator_distinct, ?_, swapped_laguerre_no_local_expression⟩
  intro n hn
  rw [laguerre_spectral_raw_action,laguerre_spectral_raw_action, swapped_laguerre_first_three n hn]
  rfl

end
end Sigma
