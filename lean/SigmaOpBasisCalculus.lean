import SigmaOpSpectralData

namespace Sigma
noncomputable section
open scoped ENNReal

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem basis_multiplier_mem (f : ι → ℂ) (hf : ∀ i, ‖f i‖ ≤ 1)
    (x : lp (fun _ : ι => ℂ) 2) : Memℓp (fun i => f i*x i) 2 := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  apply (memℓp_gen_iff hp).mpr
  have hs := x.property.summable hp
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hs ⊢
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ hs
  intro i
  rw [norm_mul, mul_pow]
  have hh : ‖f i‖^2 ≤ 1 := by nlinarith [norm_nonneg (f i), hf i]
  simpa using mul_le_mul_of_nonneg_right hh (sq_nonneg ‖x i‖)

private def basisMultiplierLinear (f : ι → ℂ) (hf : ∀ i, ‖f i‖ ≤ 1) :
    lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2 where
  toFun x := ⟨fun i => f i*x i, basis_multiplier_mem f hf x⟩
  map_add' x y := by
    apply lp.ext
    funext i
    change f i*(x i+y i) = f i*x i+f i*y i
    ring
  map_smul' a x := by
    apply lp.ext
    funext i
    change f i*(a*x i) = a*(f i*x i)
    ring

private theorem basis_multiplier_norm_le (f : ι → ℂ) (hf : ∀ i, ‖f i‖ ≤ 1)
    (x : lp (fun _ : ι => ℂ) 2) : ‖basisMultiplierLinear f hf x‖ ≤ 1*‖x‖ := by
  rw [one_mul]
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  apply lp.norm_le_of_tsum_le hp (norm_nonneg x)
  rw [lp.norm_rpow_eq_tsum hp]
  apply tsum_le_tsum _ ((basisMultiplierLinear f hf x).property.summable hp)
    (x.property.summable hp)
  intro i
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  change ‖f i*x i‖^2 ≤ ‖x i‖^2
  rw [norm_mul, mul_pow]
  have hh : ‖f i‖^2 ≤ 1 := by nlinarith [norm_nonneg (f i), hf i]
  simpa using mul_le_mul_of_nonneg_right hh (sq_nonneg ‖x i‖)

/-- Bounded spectral calculus in any complete Hilbert basis, extending the
existing integer-index multiplier to finite and empty spectral index types. -/
def basisContraction (b : HilbertBasis ι ℂ H) (f : ι → ℂ) (hf : ∀ i, ‖f i‖ ≤ 1) :
    H →L[ℂ] H :=
  b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((basisMultiplierLinear f hf).mkContinuous 1 (basis_multiplier_norm_le f hf)).comp
      b.repr.toContinuousLinearEquiv.toContinuousLinearMap)

theorem basis_contraction_coordinate (b : HilbertBasis ι ℂ H) (f : ι → ℂ)
    (hf : ∀ i, ‖f i‖ ≤ 1) (x : H) (i : ι) :
    b.repr (basisContraction b f hf x) i = f i*b.repr x i := by
  change b.repr (b.repr.symm _) i = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem basis_contraction_basis_action (b : HilbertBasis ι ℂ H) (f : ι → ℂ)
    (hf : ∀ i, ‖f i‖ ≤ 1) (i : ι) : basisContraction b f hf (b i) = f i • b i := by
  classical
  apply b.repr.injective
  apply lp.ext
  funext j
  simp only [basis_contraction_coordinate, map_smul, b.repr_self,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases h : j = i
  · subst j
    rfl
  · simp only [lp.single_apply_ne _ _ _ h, mul_zero]

theorem basis_contraction_nuclear_iff [CompleteSpace H]
    (b : HilbertBasis ι ℂ H) (f : ι → ℂ) (hf : ∀ i, ‖f i‖ ≤ 1) :
    IsNuclearOperator (basisContraction b f hf) ↔ Summable (fun i => ‖f i‖) := by
  classical
  constructor
  · intro h
    have hd := nuclear_arbitrary_basis_diagonal_summable b h
    have he (i : ι) : @inner ℂ H _ (b i) (basisContraction b f hf (b i)) = f i := by
      rw [basis_contraction_basis_action, inner_smul_right,
        ← b.repr_apply_apply, b.repr_self, lp.single_apply_self, mul_one]
    simpa only [he] using hd
  · exact arbitrary_diagonal_nuclear_of_summable b _ f (basis_contraction_basis_action b f hf)

theorem basis_contraction_trace (b : HilbertBasis ι ℂ H) (f : ι → ℂ)
    (hf : ∀ i, ‖f i‖ ≤ 1) (h : IsNuclearOperator (basisContraction b f hf)) :
    nuclearTrace (basisContraction b f hf) h = ∑' i, f i := by
  classical
  rw [nuclear_trace_eq_arbitrary_basis_sum b]
  apply tsum_congr
  intro i
  rw [basis_contraction_basis_action, inner_smul_right,
    ← b.repr_apply_apply, b.repr_self, lp.single_apply_self, mul_one]

end
end Sigma
