import SigmaOpEigenbasisEquivalence
import SigmaOpResolvent

namespace Sigma
noncomputable section

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Self-adjointness of the genuine bounded inverse is derived from the two
inverse equations and native self-adjointness of the generator. -/
theorem selfadjoint_positive_shift_resolvent
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (R : H →L[ℂ] H) (hR : OpIsResolvent A 1 R) : IsSelfAdjoint R := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  have hsymm : A.IsFormalAdjoint A := by
    have h := A.adjoint_isFormalAdjoint hA.dense_domain
    rwa [LinearPMap.isSelfAdjoint_def.mp hA] at h
  have hh := hsymm ⟨R x, hR.image_mem x⟩ ⟨R y, hR.image_mem y⟩
  have hx : A ⟨R x, hR.image_mem x⟩ = x-R x := by
    simpa using operator_resolvent_action A 1 R hR x
  have hy : A ⟨R y, hR.image_mem y⟩ = y-R y := by
    simpa using operator_resolvent_action A 1 R hR y
  rw [hx, hy, inner_sub_left, inner_sub_right] at hh
  exact (sub_left_injective hh).symm

omit [CompleteSpace H] in
theorem shift_resolvent_eigenvalue_ne_zero
    (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (hR : OpIsResolvent A 1 R)
    (v : H) (hv : v ≠ 0) (r : ℝ) (he : R v = (r : ℂ) • v) : r ≠ 0 := by
  intro hr
  have hz : R v = R 0 := by simpa [hr] using he
  exact hv (operator_resolvent_injective A 1 R hR hz)

omit [CompleteSpace H] in
/-- A nonzero resolvent eigenvalue yields membership in the full generator
domain, and its reciprocal shift is the actual generator eigenvalue. -/
theorem shift_resolvent_eigenvector_generator
    (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (hR : OpIsResolvent A 1 R)
    (v : H) (r : ℝ) (hr : r ≠ 0) (he : R v = (r : ℂ) • v) :
    ∃ hv : v ∈ A.domain, A ⟨v, hv⟩ = ((r⁻¹-1 : ℝ) : ℂ) • v := by
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hx : R ((r : ℂ)⁻¹ • v) = v := by
    rw [map_smul, he, inv_smul_smul₀ hrc]
  have hv : v ∈ A.domain := hx ▸ hR.image_mem ((r : ℂ)⁻¹ • v)
  refine ⟨hv, ?_⟩
  have hh := operator_resolvent_action A 1 R hR ((r : ℂ)⁻¹ • v)
  have heq : (⟨R ((r : ℂ)⁻¹ • v), hR.image_mem _⟩ : A.domain) = ⟨v, hv⟩ :=
    Subtype.ext hx
  rw [heq, hx, one_smul] at hh
  calc
    _ = (r : ℂ)⁻¹ • v-v := hh
    _ = ((r : ℂ)⁻¹-1) • v := by rw [sub_smul, one_smul]
    _ = _ := by push_cast; rfl

omit [CompleteSpace H] in
/-- An eigenbasis of the compact resolvent becomes a complete eigenbasis of
the unbounded generator. Its eigenvalues are nonnegative by the literal
quadratic-form hypothesis, and membership in the generator domain is derived. -/
theorem nonnegative_generator_eigenbasis_of_resolvent
    (A : H →ₗ.[ℂ] H)
    (hpos : ∀ x : A.domain, 0 ≤ (@inner ℂ H _ x.val (A x)).re)
    (R : H →L[ℂ] H) (hR : OpIsResolvent A 1 R)
    (b : HilbertBasis ι ℂ H) (r : ι → ℝ)
    (he : ∀ i, R (b i) = (r i : ℂ) • b i) :
    (∀ i, 0 ≤ (r i)⁻¹-1) ∧
      ∃ hdom : ∀ i, b i ∈ A.domain,
        ∀ i, A ⟨b i, hdom i⟩ = (((r i)⁻¹-1 : ℝ) : ℂ) • b i := by
  classical
  have hn (i : ι) : b i ≠ 0 := by
    intro hz
    have hh := b.orthonormal.1 i
    rw [hz, norm_zero] at hh
    norm_num at hh
  have hv (i : ι) := shift_resolvent_eigenvector_generator A R hR (b i) (r i)
    (shift_resolvent_eigenvalue_ne_zero A R hR (b i) (hn i) (r i) (he i)) (he i)
  have hdom (i : ι) : b i ∈ A.domain := (hv i).choose
  have ha (i : ι) : A ⟨b i, hdom i⟩ = (((r i)⁻¹-1 : ℝ) : ℂ) • b i := (hv i).choose_spec
  refine ⟨?_, hdom, ha⟩
  intro i
  have hp := hpos ⟨b i, hdom i⟩
  rw [ha, inner_smul_right, ← b.repr_apply_apply, b.repr_self,
    lp.single_apply_self, mul_one] at hp
  simpa using hp

end
end Sigma
