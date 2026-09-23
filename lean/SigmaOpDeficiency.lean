import SigmaOpCanonicalCalculus

namespace Sigma
noncomputable section

/-- The actual eigenspace of a partially defined operator, retaining its
domain. For the adjoint at plus/minus `I` this is its deficiency space. -/
def partialOperatorEigenspace
    (T : LaguerreWeightedHilbert →ₗ.[ℂ] LaguerreWeightedHilbert) (z : ℂ) :
    Submodule ℂ LaguerreWeightedHilbert where
  carrier := {x | ∃ hx : x ∈ T.domain, T ⟨x,hx⟩ = z • x}
  zero_mem' := ⟨Submodule.zero_mem _, by change T.toFun 0 = _; simp⟩
  add_mem' := by
    rintro x y ⟨hx,hTx⟩ ⟨hy,hTy⟩
    refine ⟨Submodule.add_mem _ hx hy, ?_⟩
    change T (⟨x,hx⟩ + ⟨y,hy⟩) = _
    rw [LinearPMap.map_add, hTx, hTy, smul_add]
  smul_mem' := by
    rintro c x ⟨hx,hTx⟩
    refine ⟨Submodule.smul_mem _ c hx, ?_⟩
    change T (c • ⟨x,hx⟩) = _
    rw [LinearPMap.map_smul, hTx, smul_comm]

theorem laguerre_minimal_deficiency_space_zero (z : ℂ) (hz : z.im ≠ 0) :
    partialOperatorEigenspace laguerreMinimalOperator.adjoint z = ⊥ := by
  rw [laguerre_minimal_adjoint_eq_canonical, laguerre_canonical_eq_spectral]
  apply eq_bot_iff.mpr
  rintro x ⟨hx,hTx⟩
  change x = 0
  by_contra hne
  obtain ⟨n,hn⟩ := laguerre_eigenvalue_is_integer z ⟨x,hx⟩ hne hTx
  apply hz
  rw [hn]
  simp

/-- Both deficiency spaces vanish, not merely a numerical index assigned
to the spectral model. They are the kernels of the actual minimal adjoint
minus the two nonreal spectral parameters. -/
theorem laguerre_minimal_deficiency_spaces :
    partialOperatorEigenspace laguerreMinimalOperator.adjoint Complex.I = ⊥ ∧
      partialOperatorEigenspace laguerreMinimalOperator.adjoint (-Complex.I) = ⊥ := by
  constructor
  · exact laguerre_minimal_deficiency_space_zero _ (by simp)
  · exact laguerre_minimal_deficiency_space_zero _ (by simp)

theorem laguerre_minimal_deficiency_indices :
    Module.finrank ℂ (partialOperatorEigenspace laguerreMinimalOperator.adjoint Complex.I) = 0 ∧
      Module.finrank ℂ (partialOperatorEigenspace laguerreMinimalOperator.adjoint (-Complex.I)) = 0 := by
  rw [laguerre_minimal_deficiency_spaces.1, laguerre_minimal_deficiency_spaces.2]
  simp

end
end Sigma
