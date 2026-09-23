import SigmaOpCompactResolventBasis
import SigmaOpBasisCalculus
import SigmaOpSpectralRecovery
import SigmaOpTraceInverse

namespace Sigma
noncomputable section

universe uι uκ uH uK
variable {ι : Type uι} {κ : Type uκ} {H : Type uH} {K : Type uK}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

private theorem real_heat_multiplier_bound (lam : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (t : ℝ) (ht : 0 < t) (i : ι) : ‖(Real.exp (-t * lam i) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  nlinarith [mul_nonneg (le_of_lt ht) (hlam i)]

private theorem shifted_zeta_multiplier_bound (lam : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (s : ℝ) (hs : 0 < s) (i : ι) :
    ‖(((1 + lam i)^(-s) : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (by linarith [hlam i]) _)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hlam i]) (by linarith)

/-- Equality of every finite actual heat trace in complete eigenbases recovers
the eigenvalue multiset and the unitary equivalence of the native operators. -/
theorem eigenbasis_heat_traces_recover_operator
    (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (lam : ι → ℝ) (mu : κ → ℝ) (hlam : ∀ i, 0 ≤ lam i) (hmu : ∀ j, 0 ≤ mu j)
    (A : H →ₗ.[ℂ] H) (B : K →ₗ.[ℂ] K) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hdomA : ∀ i, b i ∈ A.domain) (hdomB : ∀ j, c j ∈ B.domain)
    (ha : ∀ i, A ⟨b i, hdomA i⟩ = (lam i : ℂ) • b i)
    (hb : ∀ j, B ⟨c j, hdomB j⟩ = (mu j : ℂ) • c j)
    (hAclass : ∀ (t : ℝ) (ht : 0 < t), IsNuclearOperator
      (basisContraction b (fun i => (Real.exp (-t * lam i) : ℂ))
        (real_heat_multiplier_bound lam hlam t ht)))
    (hBclass : ∀ (t : ℝ) (ht : 0 < t), IsNuclearOperator
      (basisContraction c (fun j => (Real.exp (-t * mu j) : ℂ))
        (real_heat_multiplier_bound mu hmu t ht)))
    (htrace : ∀ t : ℝ, (ht : 0 < t) →
      nuclearTrace (basisContraction b (fun i => (Real.exp (-t * lam i) : ℂ))
        (real_heat_multiplier_bound lam hlam t ht)) (hAclass t ht) =
      nuclearTrace (basisContraction c (fun j => (Real.exp (-t * mu j) : ℂ))
        (real_heat_multiplier_bound mu hmu t ht)) (hBclass t ht)) :
    ∃ e : ι ≃ κ, (∀ i, mu (e i) = lam i) ∧
      ∃ U : H ≃ₗᵢ[ℂ] K,
        (∀ i, U (b i) = c (e i)) ∧
        (∀ x : H, U x ∈ B.domain ↔ x ∈ A.domain) ∧
        (∀ (x : A.domain) (y : B.domain), U x.val = y.val → U (A x) = B y) := by
  have hsumA (t : ℝ) (ht : 0 < t) : Summable (fun i => Real.exp (-t * lam i)) := by
    have hs := (basis_contraction_nuclear_iff b _
      (real_heat_multiplier_bound lam hlam t ht)).mp (hAclass t ht)
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hs
  have hsumB (t : ℝ) (ht : 0 < t) : Summable (fun j => Real.exp (-t * mu j)) := by
    have hs := (basis_contraction_nuclear_iff c _
      (real_heat_multiplier_bound mu hmu t ht)).mp (hBclass t ht)
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hs
  have hdata (t : ℝ) (ht : 0 < t) :
      (∑' i, Real.exp (-t * lam i)) = ∑' j, Real.exp (-t * mu j) := by
    have h := htrace t ht
    rw [basis_contraction_trace b _ _ (hAclass t ht),
      basis_contraction_trace c _ _ (hBclass t ht)] at h
    rw [← Complex.ofReal_tsum (fun i => Real.exp (-t * lam i)),
      ← Complex.ofReal_tsum (fun j => Real.exp (-t * mu j))] at h
    exact Complex.ofReal_injective h
  obtain ⟨e, he⟩ := heat_spectral_data_equiv lam mu hlam hmu 0
    (fun t ht => hsumA t ht) (fun t ht => hsumB t ht) (fun t ht => hdata t ht)
  exact ⟨e, he, real_eigenbasis_unitary_equivalence b c lam mu e he A B hA hB
    hdomA hdomB ha hb⟩

/-- Equality of every finite real shifted-zeta trace on a positive terminal
ray recovers multiplicities and hence the actual self-adjoint operators. -/
theorem eigenbasis_shifted_zeta_traces_recover_operator
    (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (lam : ι → ℝ) (mu : κ → ℝ) (hlam : ∀ i, 0 ≤ lam i) (hmu : ∀ j, 0 ≤ mu j)
    (A : H →ₗ.[ℂ] H) (B : K →ₗ.[ℂ] K) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hdomA : ∀ i, b i ∈ A.domain) (hdomB : ∀ j, c j ∈ B.domain)
    (ha : ∀ i, A ⟨b i, hdomA i⟩ = (lam i : ℂ) • b i)
    (hb : ∀ j, B ⟨c j, hdomB j⟩ = (mu j : ℂ) • c j)
    (s₀ : ℝ)
    (hAclass : ∀ (s : ℝ) (hs : max s₀ 0 < s), IsNuclearOperator
      (basisContraction b (fun i => (((1 + lam i)^(-s) : ℝ) : ℂ))
        (shifted_zeta_multiplier_bound lam hlam s (lt_of_le_of_lt (le_max_right s₀ 0) hs)))
      )
    (hBclass : ∀ (s : ℝ) (hs : max s₀ 0 < s), IsNuclearOperator
      (basisContraction c (fun j => (((1 + mu j)^(-s) : ℝ) : ℂ))
        (shifted_zeta_multiplier_bound mu hmu s (lt_of_le_of_lt (le_max_right s₀ 0) hs)))
      )
    (htrace : ∀ (s : ℝ) (hs : max s₀ 0 < s),
      nuclearTrace (basisContraction b (fun i => (((1 + lam i)^(-s) : ℝ) : ℂ))
        (shifted_zeta_multiplier_bound lam hlam s (lt_of_le_of_lt (le_max_right _ _) hs)))
        (hAclass s hs) =
      nuclearTrace (basisContraction c (fun j => (((1 + mu j)^(-s) : ℝ) : ℂ))
        (shifted_zeta_multiplier_bound mu hmu s (lt_of_le_of_lt (le_max_right _ _) hs)))
        (hBclass s hs)) :
    ∃ e : ι ≃ κ, (∀ i, mu (e i) = lam i) ∧
      ∃ U : H ≃ₗᵢ[ℂ] K,
        (∀ i, U (b i) = c (e i)) ∧
        (∀ x : H, U x ∈ B.domain ↔ x ∈ A.domain) ∧
        (∀ (x : A.domain) (y : B.domain), U x.val = y.val → U (A x) = B y) := by
  let s₁ := max s₀ 0
  have hsumA (s : ℝ) (hs : s₁ < s) : Summable (fun i => (1 + lam i)^(-s)) := by
    have hsp : 0 < s := lt_of_le_of_lt (le_max_right _ _) hs
    have hh := (basis_contraction_nuclear_iff b _
      (shifted_zeta_multiplier_bound lam hlam s hsp)).mp (hAclass s hs)
    exact hh.congr fun i => by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos (by linarith [hlam i]) _)]
  have hsumB (s : ℝ) (hs : s₁ < s) : Summable (fun j => (1 + mu j)^(-s)) := by
    have hsp : 0 < s := lt_of_le_of_lt (le_max_right _ _) hs
    have hh := (basis_contraction_nuclear_iff c _
      (shifted_zeta_multiplier_bound mu hmu s hsp)).mp (hBclass s hs)
    exact hh.congr fun j => by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos (by linarith [hmu j]) _)]
  have hdata (s : ℝ) (hs : s₁ < s) :
      (∑' i, (1 + lam i)^(-s)) = ∑' j, (1 + mu j)^(-s) := by
    have hsp : 0 < s := lt_of_le_of_lt (le_max_right _ _) hs
    have h := htrace s hs
    rw [basis_contraction_trace b _ _ (hAclass s hs),
      basis_contraction_trace c _ _ (hBclass s hs)] at h
    rw [← Complex.ofReal_tsum (fun i => (1 + lam i)^(-s)),
      ← Complex.ofReal_tsum (fun j => (1 + mu j)^(-s))] at h
    exact Complex.ofReal_injective h
  obtain ⟨e, he⟩ := zeta_spectral_data_equiv lam mu hlam hmu s₁
    (fun s hs => hsumA s hs) (fun s hs => hsumB s hs) (fun s hs => hdata s hs)
  exact ⟨e, he, real_eigenbasis_unitary_equivalence b c lam mu e he A B hA hB
    hdomA hdomB ha hb⟩

/-- The integer-trace inverse with the compact-resolvent eigenbases derived
internally, rather than supplied as extra spectral assumptions. -/
theorem compact_resolvent_integer_traces_recover_operator
    (A : H →ₗ.[ℂ] H) (B : K →ₗ.[ℂ] K)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hposA : ∀ x : A.domain, 0 ≤ (@inner ℂ H _ x.val (A x)).re)
    (hposB : ∀ x : B.domain, 0 ≤ (@inner ℂ K _ x.val (B x)).re)
    (R : H →L[ℂ] H) (S : K →L[ℂ] K)
    (hR : OpIsResolvent A 1 R) (hS : OpIsResolvent B 1 S)
    (hRcompact : IsCompactOperator R) (hScompact : IsCompactOperator S)
    (hR2 : IsNuclearOperator (R^2)) (hS2 : IsNuclearOperator (S^2))
    (htrace : ∀ (n : ℕ)
      (hRn : IsNuclearOperator (R^(n+2)))
      (hSn : IsNuclearOperator (S^(n+2))),
      nuclearTrace (R^(n+2)) hRn = nuclearTrace (S^(n+2)) hSn) :
    ∃ (ι : Type uH) (κ : Type uK) (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
      (lam : ι → ℝ) (mu : κ → ℝ),
      (∀ i, 0 ≤ lam i) ∧ (∀ j, 0 ≤ mu j) ∧
      ∃ e : ι ≃ κ, (∀ i, mu (e i) = lam i) ∧
        ∃ U : H ≃ₗᵢ[ℂ] K,
          (∀ i, U (b i) = c (e i)) ∧
          (∀ x : H, U x ∈ B.domain ↔ x ∈ A.domain) ∧
          (∀ (x : A.domain) (y : B.domain), U x.val = y.val → U (A x) = B y) := by
  obtain ⟨ι, b, lam, hlam, hdomA, ha⟩ :=
    nonnegative_compact_resolvent_eigenbasis A hA hposA R hR hRcompact
  obtain ⟨κ, c, mu, hmu, hdomB, hb⟩ :=
    nonnegative_compact_resolvent_eigenbasis B hB hposB S hS hScompact
  have htrace' (n : ℕ) :
      nuclearTrace (R^(n+2))
        (positive_shift_resolvent_higher_nuclear b lam hlam A R hR hdomA ha hR2 n) =
      nuclearTrace (S^(n+2))
        (positive_shift_resolvent_higher_nuclear c mu hmu B S hS hdomB hb hS2 n) :=
    htrace n _ _
  obtain ⟨e, he, U, hUb, hUdom, hUint⟩ :=
    integer_operator_traces_unitary_equivalence b c lam mu hlam hmu A B hA hB R S hR hS
      hdomA hdomB ha hb hR2 hS2 htrace'
  exact ⟨ι, κ, b, c, lam, mu, hlam, hmu, e, he, U, hUb, hUdom, hUint⟩

end
end Sigma
