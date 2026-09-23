import SigmaOpLaguerreComplexResolvent

namespace Sigma
noncomputable section
open scoped ComplexConjugate ENNReal NNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def integerBasisMultiplierDomain (b : HilbertBasis ℕ ℂ H) (f : ℕ → ℂ) : Submodule ℂ H where
  carrier := {x | Memℓp (fun n => f n*b.repr x n) 2}
  zero_mem' := by
    change Memℓp (fun n => f n*b.repr 0 n) 2
    simpa using (0 : MarkedIntegerHilbert).property
  add_mem' {x y} hx hy := by
    change Memℓp (fun n => f n*b.repr x n) 2 at hx
    change Memℓp (fun n => f n*b.repr y n) 2 at hy
    change Memℓp (fun n => f n*b.repr (x+y) n) 2
    convert hx.add hy using 1
    funext n
    simp only [map_add, lp.coeFn_add, Pi.add_apply]
    ring
  smul_mem' c x hx := by
    change Memℓp (fun n => f n*b.repr x n) 2 at hx
    change Memℓp (fun n => f n*b.repr (c • x) n) 2
    convert hx.const_smul c using 1
    funext n
    simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    ring

/-- Maximal spectral multiplication on the supplied Hilbert space and complete
marked basis, including the exact unbounded domain. -/
def integerBasisMultiplier (b : HilbertBasis ℕ ℂ H) (f : ℕ → ℂ) : H →ₗ.[ℂ] H where
  domain := integerBasisMultiplierDomain b f
  toFun :=
    { toFun := fun x => b.repr.symm ⟨fun n => f n*b.repr x.val n, x.property⟩
      map_add' := by
        intro x y
        apply b.repr.injective
        simp only [map_add, LinearIsometryEquiv.apply_symm_apply]
        apply lp.ext
        funext n
        change f n*b.repr (x.val+y.val) n = f n*b.repr x.val n+f n*b.repr y.val n
        simp only [map_add, lp.coeFn_add, Pi.add_apply]
        ring
      map_smul' := by
        intro c x
        apply b.repr.injective
        simp only [map_smul, LinearIsometryEquiv.apply_symm_apply]
        apply lp.ext
        funext n
        change f n*b.repr (c • x.val) n = c*(f n*b.repr x.val n)
        simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
        ring }

theorem integer_basis_multiplier_coordinate (b : HilbertBasis ℕ ℂ H) (f : ℕ → ℂ)
    (x : (integerBasisMultiplier b f).domain) (n : ℕ) :
    b.repr (integerBasisMultiplier b f x) n = f n*b.repr x.val n := by
  change b.repr (b.repr.symm _) n = _
  rw [LinearIsometryEquiv.apply_symm_apply]

theorem integer_basis_multiplier_domain_iff (b : HilbertBasis ℕ ℂ H) (f : ℕ → ℂ) (x : H) :
    x ∈ (integerBasisMultiplier b f).domain ↔
      Summable (fun n => ‖f n‖^2*‖b.repr x n‖^2) := by
  change Memℓp (fun n => f n*b.repr x n) 2 ↔ _
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_mul, mul_pow]

theorem integer_basis_mem_multiplier_domain (b : HilbertBasis ℕ ℂ H) (f : ℕ → ℂ) (n : ℕ) :
    b n ∈ (integerBasisMultiplier b f).domain := by
  change Memℓp (fun k => f k*b.repr (b n) k) 2
  rw [b.repr_self]
  have he : (fun k => f k*(lp.single (E := fun _ : ℕ => ℂ) 2 n 1) k) =
      fun k => (lp.single (E := fun _ : ℕ => ℂ) 2 n (f n)) k := by
    funext k
    by_cases hk : k = n
    · subst k
      simp only [lp.single_apply_self, mul_one]
    · simp only [lp.single_apply_ne _ _ _ hk, mul_zero]
  rw [he]
  exact (lp.single (E := fun _ : ℕ => ℂ) 2 n (f n)).property

theorem integer_basis_multiplier_basis_action (b : HilbertBasis ℕ ℂ H) (f : ℕ → ℂ) (n : ℕ) :
    integerBasisMultiplier b f ⟨b n, integer_basis_mem_multiplier_domain b f n⟩ = f n • b n := by
  apply b.repr.injective
  apply lp.ext
  funext k
  simp only [integer_basis_multiplier_coordinate, map_smul, b.repr_self,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases hk : k = n
  · subst k
    rfl
  · simp only [lp.single_apply_ne _ _ _ hk, mul_zero]

theorem integer_basis_multiplier_formal_adjoint (b : HilbertBasis ℕ ℂ H) (f : ℕ → ℂ)
    (hf : ∀ n, conj (f n) = f n) :
    (integerBasisMultiplier b f).IsFormalAdjoint (integerBasisMultiplier b f) := by
  intro x y
  rw [← b.repr.inner_map_map, ← b.repr.inner_map_map, lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  rw [integer_basis_multiplier_coordinate, integer_basis_multiplier_coordinate]
  simp only [RCLike.inner_apply, map_mul, hf]
  ring

/-- The supplied self-adjoint operator is identified on its ENTIRE maximal
domain, not merely on the finite span of its complete eigenbasis. -/
theorem integer_eigenbasis_operator_eq [CompleteSpace H] (b : HilbertBasis ℕ ℂ H)
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (hdom : ∀ n : ℕ, b n ∈ A.domain)
    (ha : ∀ n : ℕ, A ⟨b n, hdom n⟩ = (n : ℂ) • b n) :
    A = integerBasisMultiplier b (fun n => (n : ℂ)) := by
  have hsymm : A.IsFormalAdjoint A := by
    have h := A.adjoint_isFormalAdjoint hA.dense_domain
    rwa [LinearPMap.isSelfAdjoint_def.mp hA] at h
  have hc (x : A.domain) (n : ℕ) : b.repr (A x) n = (n : ℂ)*b.repr x.val n := by
    have h := hsymm ⟨b n, hdom n⟩ x
    rw [ha, inner_smul_left] at h
    simpa [b.repr_apply_apply] using h.symm
  have hle : A ≤ integerBasisMultiplier b (fun n => (n : ℂ)) := by
    refine ⟨?_, ?_⟩
    · intro x hx
      change Memℓp (fun n : ℕ => (n : ℂ)*b.repr x n) 2
      have he : (fun n : ℕ => (n : ℂ)*b.repr x n) = fun n => b.repr (A ⟨x,hx⟩) n := by
        funext n
        exact (hc ⟨x,hx⟩ n).symm
      rw [he]
      exact (b.repr (A ⟨x,hx⟩)).property
    · intro x y hxy
      apply b.repr.injective
      apply lp.ext
      funext n
      rw [hc, integer_basis_multiplier_coordinate, hxy]
  apply le_antisymm hle
  have hST : A.IsFormalAdjoint (integerBasisMultiplier b (fun n => (n : ℂ))) := by
    intro x y
    have h := integer_basis_multiplier_formal_adjoint b (fun n => (n : ℂ))
      (by intro n; simp) ⟨x.val, hle.1 x.property⟩ y
    rwa [← hle.2 (x := x) rfl] at h
  have hh := hST.le_adjoint hA.dense_domain
  rwa [LinearPMap.isSelfAdjoint_def.mp hA] at hh

def integerBasisBoundedMultiplier (b : HilbertBasis ℕ ℂ H) (f : ℕ → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C) : H →L[ℂ] H :=
  b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((markedComplexDiagonalLinear f C hf).mkContinuous C
      (marked_complex_diagonal_norm f C hC hf)).comp
      b.repr.toContinuousLinearEquiv.toContinuousLinearMap)

theorem integer_basis_bounded_multiplier_coordinate (b : HilbertBasis ℕ ℂ H) (f : ℕ → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C) (x : H) (n : ℕ) :
    b.repr (integerBasisBoundedMultiplier b f C hC hf x) n = f n*b.repr x n := by
  change b.repr (b.repr.symm _) n = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem integer_basis_bounded_multiplier_mem_domain (b : HilbertBasis ℕ ℂ H) (f : ℕ → ℂ)
    (C : ℝ) (hf : ∀ n, ‖f n‖ ≤ C) (x : H) :
    x ∈ (integerBasisMultiplier b f).domain :=
  marked_complex_multiplier_mem f C hf (b.repr x)

theorem integer_basis_bounded_multiplier_eq (b : HilbertBasis ℕ ℂ H) (f : ℕ → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C) :
    integerBasisMultiplier b f = (integerBasisBoundedMultiplier b f C hC hf).toLinearMap.toPMap ⊤ := by
  apply LinearPMap.ext
  · apply top_unique
    intro x _
    exact integer_basis_bounded_multiplier_mem_domain b f C hf x
  · intro x y hxy
    apply b.repr.injective
    apply lp.ext
    funext n
    rw [integer_basis_multiplier_coordinate]
    change f n*b.repr x.val n = b.repr (integerBasisBoundedMultiplier b f C hC hf y.val) n
    rw [integer_basis_bounded_multiplier_coordinate, hxy]

theorem integer_eigenbasis_domain_iff [CompleteSpace H] (b : HilbertBasis ℕ ℂ H)
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (hdom : ∀ n : ℕ, b n ∈ A.domain)
    (ha : ∀ n : ℕ, A ⟨b n, hdom n⟩ = (n : ℂ) • b n) (x : H) :
    x ∈ A.domain ↔ Summable (fun n : ℕ => (n : ℝ)^2*‖b.repr x n‖^2) := by
  rw [integer_eigenbasis_operator_eq b A hA hdom ha, integer_basis_multiplier_domain_iff]
  simp only [Complex.norm_natCast]

theorem integer_eigenbasis_coordinate [CompleteSpace H] (b : HilbertBasis ℕ ℂ H)
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (hdom : ∀ n : ℕ, b n ∈ A.domain)
    (ha : ∀ n : ℕ, A ⟨b n, hdom n⟩ = (n : ℂ) • b n)
    (x : A.domain) (n : ℕ) : b.repr (A x) n = (n : ℂ)*b.repr x.val n := by
  have he := integer_eigenbasis_operator_eq b A hA hdom ha
  have hx : A x = integerBasisMultiplier b (fun n : ℕ => (n : ℂ))
      ⟨x.val, he.le.1 x.property⟩ := he.le.2 rfl
  rw [hx, integer_basis_multiplier_coordinate]

theorem integer_basis_bounded_multiplier_basis_action (b : HilbertBasis ℕ ℂ H) (f : ℕ → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C) (n : ℕ) :
    integerBasisBoundedMultiplier b f C hC hf (b n) = f n • b n := by
  apply b.repr.injective
  apply lp.ext
  funext k
  simp only [integer_basis_bounded_multiplier_coordinate, map_smul, b.repr_self,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases hk : k = n
  · subst k
    rfl
  · simp only [lp.single_apply_ne _ _ _ hk, mul_zero]

end
end Sigma
