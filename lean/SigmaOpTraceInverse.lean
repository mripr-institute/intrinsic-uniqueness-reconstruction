import SigmaOpSpectralData
import SigmaOpSpectralRecovery
import SigmaOpEigenbasisEquivalence
import SigmaOpResolvent

namespace Sigma
noncomputable section

variable {ι κ H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] in
/-- The inverse equations themselves extract the spectral samples of an actual
resolvent. No diagonal action for the resolvent is assumed. -/
theorem positive_shift_resolvent_eigenvector
    (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (hR : OpIsResolvent A 1 R)
    (v : A.domain) (t : ℝ) (ht : 0 ≤ t) (hv : A v = (t : ℂ) • v.val) :
    R v.val = (((1+t)⁻¹ : ℝ) : ℂ) • v.val := by
  have he := hR.left_inverse v
  rw [hv, ← add_smul, map_smul] at he
  have hne : (t : ℂ)+1 ≠ 0 := by
    have hp : t+1 > 0 := by linarith
    exact_mod_cast hp.ne'
  calc
    R v.val = ((t : ℂ)+1)⁻¹ • (((t : ℂ)+1) • R v.val) := by
      rw [inv_smul_smul₀ hne]
    _ = ((t : ℂ)+1)⁻¹ • v.val := by rw [he]
    _ = _ := by push_cast; rw [add_comm]

omit [CompleteSpace H] in
theorem positive_shift_resolvent_power_eigenvector
    (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (hR : OpIsResolvent A 1 R)
    (v : A.domain) (t : ℝ) (ht : 0 ≤ t) (hv : A v = (t : ℂ) • v.val) (n : ℕ) :
    (R^n) v.val = ((((1+t)⁻¹)^n : ℝ) : ℂ) • v.val := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, ih, map_smul,
      positive_shift_resolvent_eigenvector A R hR v t ht hv, smul_smul]
    congr 1
    push_cast
    rw [pow_succ]

theorem positive_shift_resolvent_higher_nuclear
    (b : HilbertBasis ι ℂ H) (lam : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (hR : OpIsResolvent A 1 R)
    (hdom : ∀ i, b i ∈ A.domain)
    (ha : ∀ i, A ⟨b i, hdom i⟩ = (lam i : ℂ) • b i)
    (h2 : IsNuclearOperator (R^2)) (n : ℕ) : IsNuclearOperator (R^(n+2)) := by
  apply nuclear_spectral_higher_power b
    (fun i => reciprocalSpectralCoordinate (lam i) (hlam i)) 2 n (R^2) (R^(n+2))
  · intro i
    exact positive_shift_resolvent_power_eigenvector A R hR ⟨b i, hdom i⟩ _ (hlam i) (ha i) 2
  · intro i
    exact positive_shift_resolvent_power_eigenvector A R hR ⟨b i, hdom i⟩ _ (hlam i) (ha i) (n+2)
  · exact h2

/-- Actual integer shifted traces recover the finite weighted spectral measure;
its moments come from powers of the genuine inverse of 1+A. -/
theorem positive_shift_resolvent_trace_moment
    (b : HilbertBasis ι ℂ H) (lam : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (hR : OpIsResolvent A 1 R)
    (hdom : ∀ i, b i ∈ A.domain)
    (ha : ∀ i, A ⟨b i, hdom i⟩ = (lam i : ℂ) • b i)
    (h2 : IsNuclearOperator (R^2)) (n : ℕ) :
    nuclearTrace (R^(n+2)) (positive_shift_resolvent_higher_nuclear b lam hlam A R hR hdom ha h2 n) =
      ((∫ y : OpUnitInterval, (y : ℝ)^n ∂spectralWeightedMeasure
        (fun i => reciprocalSpectralCoordinate (lam i) (hlam i)) 2 : ℝ) : ℂ) := by
  apply nuclear_integer_trace_eq_spectral_moment b _ 2 n (R^2) (R^(n+2))
  · intro i
    exact positive_shift_resolvent_power_eigenvector A R hR ⟨b i, hdom i⟩ _ (hlam i) (ha i) 2
  · intro i
    exact positive_shift_resolvent_power_eigenvector A R hR ⟨b i, hdom i⟩ _ (hlam i) (ha i) (n+2)
  · exact h2

/-- Reconstruction from traces of actual resolvent powers. Complete eigenbases
are explicit inputs here; their derivation from compact resolvent is separate. -/
theorem integer_operator_traces_unitary_equivalence
    (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (lam : ι → ℝ) (mu : κ → ℝ) (hlam : ∀ i, 0 ≤ lam i) (hmu : ∀ j, 0 ≤ mu j)
    (A : H →ₗ.[ℂ] H) (B : K →ₗ.[ℂ] K) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (R : H →L[ℂ] H) (S : K →L[ℂ] K) (hR : OpIsResolvent A 1 R) (hS : OpIsResolvent B 1 S)
    (hdomA : ∀ i, b i ∈ A.domain) (hdomB : ∀ j, c j ∈ B.domain)
    (ha : ∀ i, A ⟨b i, hdomA i⟩ = (lam i : ℂ) • b i)
    (hb : ∀ j, B ⟨c j, hdomB j⟩ = (mu j : ℂ) • c j)
    (hR2 : IsNuclearOperator (R^2)) (hS2 : IsNuclearOperator (S^2))
    (htrace : ∀ n : ℕ,
      nuclearTrace (R^(n+2)) (positive_shift_resolvent_higher_nuclear b lam hlam A R hR hdomA ha hR2 n) =
      nuclearTrace (S^(n+2)) (positive_shift_resolvent_higher_nuclear c mu hmu B S hS hdomB hb hS2 n)) :
    ∃ e : ι ≃ κ, (∀ i, mu (e i) = lam i) ∧
      ∃ U : H ≃ₗᵢ[ℂ] K,
        (∀ i, U (b i) = c (e i)) ∧
        (∀ x : H, U x ∈ B.domain ↔ x ∈ A.domain) ∧
        (∀ (x : A.domain) (y : B.domain), U x.val = y.val → U (A x) = B y) := by
  have hRa (n : ℕ) (i : ι) :
      (R^n) (b i) = ((((1+lam i)⁻¹)^n : ℝ) : ℂ) • b i :=
    positive_shift_resolvent_power_eigenvector A R hR ⟨b i, hdomA i⟩ _ (hlam i) (ha i) n
  have hSa (n : ℕ) (j : κ) :
      (S^n) (c j) = ((((1+mu j)⁻¹)^n : ℝ) : ℂ) • c j :=
    positive_shift_resolvent_power_eigenvector B S hS ⟨c j, hdomB j⟩ _ (hmu j) (hb j) n
  have hRs := nuclear_spectral_power_summable b
    (fun i => reciprocalSpectralCoordinate (lam i) (hlam i)) 2 (R^2) (hRa 2) hR2
  have hSs := nuclear_spectral_power_summable c
    (fun j => reciprocalSpectralCoordinate (mu j) (hmu j)) 2 (S^2) (hSa 2) hS2
  have hm (n : ℕ) : (∑' i, ((1+lam i)⁻¹)^(n+2)) = ∑' j, ((1+mu j)⁻¹)^(n+2) := by
    have ht := htrace n
    rw [(nuclear_positive_diagonal_summable_trace b _ _
      (fun i => pow_nonneg (inv_nonneg.mpr (by linarith [hlam i])) _) (hRa (n+2)) _).2,
      (nuclear_positive_diagonal_summable_trace c _ _
      (fun j => pow_nonneg (inv_nonneg.mpr (by linarith [hmu j])) _) (hSa (n+2)) _).2] at ht
    exact_mod_cast ht
  obtain ⟨e, he⟩ := integer_shifted_spectral_data_equiv lam mu hlam hmu 2 hRs hSs hm
  exact ⟨e, he, real_eigenbasis_unitary_equivalence b c lam mu e he A B hA hB hdomA hdomB ha hb⟩

end
end Sigma
