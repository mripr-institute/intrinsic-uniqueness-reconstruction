import SigmaOpDeterminantCompact
import SigmaOpLaguerreResolventTrace

namespace Sigma
noncomputable section
set_option maxHeartbeats 800000

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A square-summable native self-adjoint operator has a nuclear square,
proved directly from its rank-one expansion in the given Hilbert basis. -/
theorem determinant_hilbert_schmidt_square_nuclear (R : H →L[ℂ] H)
    (hself : IsSelfAdjoint R) (hHS : IsHilbertSchmidtOperator R) :
    IsNuclearOperator (R^2) := by
  obtain ⟨b, hb⟩ := hHS
  have hs : Summable (fun n => rankOneOperator (R (b n)) (R (b n))) :=
    (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => rankOneOperator_norm_le _ _) (by simpa only [pow_two] using hb)).of_norm
  have he : (∑' n, rankOneOperator (R (b n)) (R (b n))) = R^2 := by
    ext x
    have hh := R.hasSum (b.hasSum_repr (R x))
    have hv := hs.hasSum.mapL (ContinuousLinearMap.apply ℂ H x)
    have hi (n : ℕ) : @inner ℂ H _ (R (b n)) x = @inner ℂ H _ (b n) (R x) :=
      hself.isSymmetric (b n) x
    simp only [map_smul, HilbertBasis.repr_apply_apply] at hh
    simp only [ContinuousLinearMap.apply_apply, rankOneOperator_apply, hi] at hv
    exact hv.unique hh
  exact ⟨fun n => R (b n), fun n => R (b n), by simpa only [pow_two] using hb,
    he ▸ hs.hasSum⟩

end
end Sigma
