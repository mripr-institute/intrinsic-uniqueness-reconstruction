import SigmaOpLaguerreDomains
import SigmaOpZetaTrace
import SigmaOpDeterminantZeta
import SigmaOpCanonicalCalculus

namespace Sigma
noncomputable section
open Filter
open scoped Topology BigOperators

/-- Replacement of finitely many shifted eigenvalues; the unselected infinite
tail is the original positive integer sequence. -/
def finiteShiftedSpectrum {N : ℕ} (e : Fin N ↪ ℕ) (r : Fin N → ℝ) : ℕ → ℝ :=
  Function.extend e r (fun n => (n : ℝ)+1)

theorem finite_shifted_spectrum_selected {N : ℕ} (e : Fin N ↪ ℕ)
    (r : Fin N → ℝ) (j : Fin N) : finiteShiftedSpectrum e r (e j) = r j :=
  e.injective.extend_apply _ _ _

theorem finite_shifted_spectrum_unselected {N : ℕ} (e : Fin N ↪ ℕ)
    (r : Fin N → ℝ) (n : ℕ) (hn : n ∉ Set.range e) :
    finiteShiftedSpectrum e r n = (n : ℝ)+1 :=
  Function.extend_apply' _ _ _ hn

theorem finite_shifted_spectrum_tail {N : ℕ} (e : Fin N ↪ ℕ) (r : Fin N → ℝ) :
    finiteShiftedSpectrum e r =ᶠ[cofinite] (fun n => (n : ℝ)+1) := by
  filter_upwards [(Set.finite_range e).compl_mem_cofinite] with n hn
  exact finite_shifted_spectrum_unselected e r n hn

theorem finite_shifted_spectrum_ge_one {N : ℕ} (e : Fin N ↪ ℕ)
    (r : Fin N → ℝ) (hr : ∀ j, 1 ≤ r j) (n : ℕ) :
    1 ≤ finiteShiftedSpectrum e r n := by
  by_cases hn : n ∈ Set.range e
  · obtain ⟨j,rfl⟩ := hn
    rw [finite_shifted_spectrum_selected]
    exact hr j
  · rw [finite_shifted_spectrum_unselected e r n hn]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

/-- The full, maximally defined native self-adjoint operator. -/
def finitePerturbedOperator {N : ℕ} (e : Fin N ↪ ℕ) (r : Fin N → ℝ) :
    LaguerreWeightedHilbert →ₗ.[ℂ] LaguerreWeightedHilbert :=
  laguerreSpectralOperator (fun t => finiteShiftedSpectrum e r ⌊t⌋₊ - 1)

theorem finite_perturbed_operator_selfadjoint {N : ℕ} (e : Fin N ↪ ℕ)
    (r : Fin N → ℝ) : IsSelfAdjoint (finitePerturbedOperator e r) :=
  laguerre_spectral_selfAdjoint _

theorem finite_perturbed_operator_nonnegative {N : ℕ} (e : Fin N ↪ ℕ)
    (r : Fin N → ℝ) (hr : ∀ j, 1 ≤ r j)
    (x : (finitePerturbedOperator e r).domain) :
    0 ≤ (@inner ℂ LaguerreWeightedHilbert _ x.val
      (finitePerturbedOperator e r x)).re := by
  apply laguerre_spectral_nonnegative
  intro n
  simpa using sub_nonneg.mpr (finite_shifted_spectrum_ge_one e r hr n)

theorem finite_perturbed_operator_basis_action {N : ℕ} (e : Fin N ↪ ℕ)
    (r : Fin N → ℝ) (n : ℕ) :
    finitePerturbedOperator e r
      ⟨laguerreHilbertBasis n,laguerre_basis_mem_spectral_domain _ n⟩ =
      ((finiteShiftedSpectrum e r n - 1 : ℝ) : ℂ) • laguerreHilbertBasis n := by
  simpa [finitePerturbedOperator] using
    laguerre_spectral_basis_action (fun t => finiteShiftedSpectrum e r ⌊t⌋₊ - 1) n

/-- Every absolute spectral convergence domain is unchanged by the finite
replacement, independently of which heat/zeta/resolvent function is used. -/
theorem finite_perturbed_summability_iff {N : ℕ} (e : Fin N ↪ ℕ)
    (r : Fin N → ℝ) (f : ℝ → ℝ) :
    Summable (fun n => f (finiteShiftedSpectrum e r n)) ↔
      Summable (fun n : ℕ => f ((n : ℝ)+1)) :=
  summable_congr_cofinite ((finite_shifted_spectrum_tail e r).fun_comp f)

/-- Entire finite correction to the continued shifted zeta function. -/
def finiteZetaCorrection {N : ℕ} (e : Fin N ↪ ℕ) (r : Fin N → ℝ) (s : ℂ) : ℂ :=
  ∑ j, (Complex.exp (-s*(Real.log (r j) : ℂ)) -
    Complex.exp (-s*(Real.log ((e j : ℝ)+1) : ℂ)))

def finitePerturbedZeta {N : ℕ} (e : Fin N ↪ ℕ) (r : Fin N → ℝ) (s : ℂ) : ℂ :=
  riemannZeta s + finiteZetaCorrection e r s

theorem finite_zeta_correction_entire {N : ℕ} (e : Fin N ↪ ℕ) (r : Fin N → ℝ) :
    Differentiable ℂ (finiteZetaCorrection e r) := by
  intro s
  apply DifferentiableAt.sum
  intro j _
  exact ((differentiableAt_id.neg.mul_const _).cexp).sub
    ((differentiableAt_id.neg.mul_const _).cexp)

theorem finite_zeta_correction_zero {N : ℕ} (e : Fin N ↪ ℕ) (r : Fin N → ℝ) :
    finiteZetaCorrection e r 0 = 0 := by simp [finiteZetaCorrection]

theorem finite_perturbed_zeta_zero {N : ℕ} (e : Fin N ↪ ℕ) (r : Fin N → ℝ) :
    finitePerturbedZeta e r 0 = riemannZeta 0 := by
  simp [finitePerturbedZeta,finite_zeta_correction_zero]

theorem finite_zeta_correction_deriv_zero {N : ℕ} (e : Fin N ↪ ℕ)
    (r : Fin N → ℝ) :
    deriv (finiteZetaCorrection e r) 0 =
      -∑ j, (Real.log (r j) : ℂ) + ∑ j, (Real.log ((e j : ℝ)+1) : ℂ) := by
  unfold finiteZetaCorrection
  have hd (j : Fin N) : HasDerivAt
      (fun s : ℂ => Complex.exp (-s*(Real.log (r j) : ℂ)) -
        Complex.exp (-s*(Real.log ((e j : ℝ)+1) : ℂ)))
      (-(Real.log (r j) : ℂ)+(Real.log ((e j : ℝ)+1) : ℂ)) 0 := by
    simpa using (((hasDerivAt_id (0 : ℂ)).neg.mul_const _).cexp).sub
      (((hasDerivAt_id (0 : ℂ)).neg.mul_const _).cexp)
  simpa [finiteZetaCorrection, Finset.sum_add_distrib, Finset.sum_neg_distrib] using
    (HasDerivAt.sum (u := Finset.univ) (fun j _ => hd j)).deriv

theorem finite_perturbed_zeta_regular {N : ℕ} (e : Fin N ↪ ℕ)
    (r : Fin N → ℝ) (s : ℂ) (hs : s ≠ 1) :
    DifferentiableAt ℂ (finitePerturbedZeta e r) s :=
  (differentiableAt_riemannZeta hs).add (finite_zeta_correction_entire e r s)

theorem finite_perturbed_zeta_residue {N : ℕ} (e : Fin N ↪ ℕ) (r : Fin N → ℝ) :
    Tendsto (fun s : ℂ => (s-1)*finitePerturbedZeta e r s)
      (𝓝[≠] 1) (𝓝 1) := by
  have hc : Tendsto (fun s : ℂ => (s-1)*finiteZetaCorrection e r s)
      (𝓝[≠] 1) (𝓝 0) := by
    have h : ContinuousAt (fun s : ℂ => (s-1)*finiteZetaCorrection e r s) 1 :=
      (continuousAt_id.sub continuousAt_const).mul
        (finite_zeta_correction_entire e r 1).continuousAt
    simpa using h.tendsto.mono_left (nhdsWithin_le_nhds (s := {1}ᶜ))
  simpa [finitePerturbedZeta,mul_add] using riemannZeta_residue_one.add hc

theorem finite_positive_cpow (r : ℝ) (hr : 0 < r) (s : ℂ) :
    1 / (r : ℂ)^s = Complex.exp (-s*(Real.log r : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'),
    ← Complex.ofReal_log hr.le,one_div,← Complex.exp_neg]
  congr 1
  ring

def finiteZetaMultiplier {N : ℕ} (e : Fin N ↪ ℕ) (r : Fin N → ℝ)
    (s : ℂ) (n : ℕ) : ℂ := 1 / (finiteShiftedSpectrum e r n : ℂ)^s

theorem finite_zeta_multiplier_norm_summable_iff {N : ℕ} (e : Fin N ↪ ℕ)
    (r : Fin N → ℝ) (s : ℂ) :
    Summable (fun n => ‖finiteZetaMultiplier e r s n‖) ↔ 1 < s.re := by
  rw [← integer_zeta_multiplier_norm_summable_iff]
  apply summable_congr_cofinite
  filter_upwards [finite_shifted_spectrum_tail e r] with n hn
  simp [finiteZetaMultiplier,hn,integerZetaMultiplier]

theorem finite_zeta_multiplier_hasSum {N : ℕ} (e : Fin N ↪ ℕ)
    (r : Fin N → ℝ) (hr : ∀ j, 0 < r j) (s : ℂ) (hs : 1 < s.re) :
    HasSum (finiteZetaMultiplier e r s) (finitePerturbedZeta e r s) := by
  classical
  let d : Fin N → ℂ := fun j => Complex.exp (-s*(Real.log (r j) : ℂ)) -
    Complex.exp (-s*(Real.log ((e j : ℝ)+1) : ℂ))
  have hd : HasSum (fun n : ℕ => ∑ j, if n = e j then d j else 0) (∑ j,d j) :=
    hasSum_sum (fun j _ => hasSum_ite_eq (e j) (d j))
  have h := (integer_zeta_multiplier_hasSum s hs).add hd
  apply h.congr_fun
  intro n
  by_cases hn : n ∈ Set.range e
  · obtain ⟨j,rfl⟩ := hn
    have hsum : (∑ k : Fin N, if e j = e k then d k else 0) = d j := by
      simp only [e.injective.eq_iff]
      simp
    rw [hsum]
    dsimp [finiteZetaMultiplier]
    rw [finite_shifted_spectrum_selected,finite_positive_cpow _ (hr j)]
    have hp : 0 < (e j : ℝ)+1 := by positivity
    have he : integerZetaMultiplier s (e j) =
        Complex.exp (-s*(Real.log ((e j : ℝ)+1) : ℂ)) := by
      simpa [integerZetaMultiplier] using finite_positive_cpow _ hp s
    rw [he]
    dsimp [d]
    ring
  · have hsum : (∑ j : Fin N, if n = e j then d j else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      exact if_neg (fun h => hn ⟨j,h.symm⟩)
    rw [hsum,add_zero]
    simp [finiteZetaMultiplier,finite_shifted_spectrum_unselected e r n hn,
      integerZetaMultiplier]

private theorem finite_zeta_multiplier_bound {N : ℕ} (e : Fin N ↪ ℕ)
    (r : Fin N → ℝ) (s : ℂ) (hs : 1 < s.re) (n : ℕ) :
    ‖finiteZetaMultiplier e r s n‖ ≤ ∑' k, ‖finiteZetaMultiplier e r s k‖ :=
  le_tsum ((finite_zeta_multiplier_norm_summable_iff e r s).mpr hs) n
    (fun _ _ => norm_nonneg _)

def finitePerturbedZetaOperator {N : ℕ} (e : Fin N ↪ ℕ)
    (r : Fin N → ℝ) (s : ℂ) (hs : 1 < s.re) :
    LaguerreWeightedHilbert →L[ℂ] LaguerreWeightedHilbert :=
  integerBasisBoundedMultiplier laguerreHilbertBasis (finiteZetaMultiplier e r s)
    (∑' k, ‖finiteZetaMultiplier e r s k‖) (tsum_nonneg fun _ => norm_nonneg _)
    (finite_zeta_multiplier_bound e r s hs)

theorem finite_perturbed_zeta_operator_basis {N : ℕ} (e : Fin N ↪ ℕ)
    (r : Fin N → ℝ) (s : ℂ) (hs : 1 < s.re) (n : ℕ) :
    finitePerturbedZetaOperator e r s hs (laguerreHilbertBasis n) =
      finiteZetaMultiplier e r s n • laguerreHilbertBasis n :=
  integer_basis_bounded_multiplier_basis_action _ _ _ _ _ _

theorem finite_perturbed_zeta_operator_nuclear {N : ℕ} (e : Fin N ↪ ℕ)
    (r : Fin N → ℝ) (s : ℂ) (hs : 1 < s.re) :
    IsNuclearOperator (finitePerturbedZetaOperator e r s hs) :=
  diagonal_operator_nuclear_of_summable laguerreHilbertBasis _ _
    (finite_perturbed_zeta_operator_basis e r s hs)
    ((finite_zeta_multiplier_norm_summable_iff e r s).mpr hs)

theorem finite_perturbed_zeta_trace {N : ℕ} (e : Fin N ↪ ℕ)
    (r : Fin N → ℝ) (hr : ∀ j, 0 < r j) (s : ℂ) (hs : 1 < s.re) :
    nuclearTrace (finitePerturbedZetaOperator e r s hs)
      (finite_perturbed_zeta_operator_nuclear e r s hs) = finitePerturbedZeta e r s := by
  rw [diagonal_operator_nuclear_trace laguerreHilbertBasis _ _
    (finite_perturbed_zeta_operator_basis e r s hs)]
  exact (finite_zeta_multiplier_hasSum e r hr s hs).tsum_eq

theorem finite_zeta_correction_real {N : ℕ} (e : Fin N ↪ ℕ)
    (r : Fin N → ℝ) (s : ℝ) :
    finiteZetaCorrection e r (s : ℂ) =
      ((∑ j, Real.exp (-s*Real.log (r j))) -
        (∑ j, Real.exp (-s*Real.log ((e j : ℝ)+1))) : ℝ) := by
  simp only [finiteZetaCorrection,Complex.ofReal_sub,Complex.ofReal_sum,
    Complex.ofReal_exp,Complex.ofReal_mul,Complex.ofReal_neg,Finset.sum_sub_distrib]

def finitePerturbedZetaDeterminant {N : ℕ} (e : Fin N ↪ ℕ)
    (r : Fin N → ℝ) : ℂ := Complex.exp (-deriv (finitePerturbedZeta e r) 0)

theorem finite_perturbed_determinant_preserved {N : ℕ} (e : Fin N ↪ ℕ)
    (r : Fin N → ℝ)
    (hlog : (∑ j,Real.log (r j)) = ∑ j,Real.log ((e j : ℝ)+1)) :
    finitePerturbedZetaDeterminant e r = laguerreZetaDeterminant 1 := by
  have hc : deriv (finiteZetaCorrection e r) 0 = 0 := by
    rw [finite_zeta_correction_deriv_zero,← Complex.ofReal_sum,← Complex.ofReal_sum,hlog]
    ring
  have hd : deriv (finitePerturbedZeta e r) 0 = deriv riemannZeta 0 := by
    unfold finitePerturbedZeta
    rw [deriv_add (differentiableAt_riemannZeta zero_ne_one)
      (finite_zeta_correction_entire e r 0),hc,add_zero]
  rw [finitePerturbedZetaDeterminant,hd,laguerre_zeta_determinant_one]

/-- Equality of the finite parts is expressed without depending on the chosen
value of a meromorphic function at its pole. -/
theorem finite_perturbed_finite_part_iff {N : ℕ} (e : Fin N ↪ ℕ)
    (r : Fin N → ℝ) (hc : finiteZetaCorrection e r 1 = 0) (L : ℂ) :
    Tendsto (fun s : ℂ => finitePerturbedZeta e r s - 1/(s-1))
      (𝓝[≠] 1) (𝓝 L) ↔
    Tendsto (fun s : ℂ => riemannZeta s - 1/(s-1)) (𝓝[≠] 1) (𝓝 L) := by
  have ht : Tendsto (finiteZetaCorrection e r) (𝓝[≠] 1) (𝓝 0) := by
    simpa only [hc] using (finite_zeta_correction_entire e r 1).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := {1}ᶜ))
  constructor
  · intro h
    have hh := h.sub ht
    convert hh using 1
    · funext s; dsimp [finitePerturbedZeta]; ring
    · simp
  · intro h
    have hh := h.add ht
    convert hh using 1
    · funext s; dsimp [finitePerturbedZeta]; ring
    · simp

theorem finite_perturbed_initial_operator {N : ℕ} (e : Fin N ↪ ℕ) :
    finitePerturbedOperator e (fun j => (e j : ℝ)+1) =
      laguerreSpectralOperator id := by
  apply laguerre_spectral_congr
  intro n
  simp only [Nat.floor_natCast,id_eq]
  by_cases hn : n ∈ Set.range e
  · obtain ⟨j,rfl⟩ := hn
    rw [finite_shifted_spectrum_selected]
    ring
  · rw [finite_shifted_spectrum_unselected e _ n hn]
    ring

theorem finite_perturbed_domain_eq {N : ℕ} (e : Fin N ↪ ℕ) (r : Fin N → ℝ) :
    (finitePerturbedOperator e r).domain = (laguerreSpectralOperator id).domain := by
  ext x
  rw [finitePerturbedOperator,laguerre_spectral_domain_iff,laguerre_spectral_domain_iff]
  apply summable_congr_cofinite
  filter_upwards [finite_shifted_spectrum_tail e r] with n hn
  simp [hn]

/-- Subtracting any proposed principal part has an analytic remainder exactly
when it does for the original zeta function. Equality is on a punctured
neighborhood, so arbitrary values assigned at poles play no role. -/
theorem finite_perturbed_principal_part_iff {N : ℕ} (e : Fin N ↪ ℕ)
    (r : Fin N → ℝ) (p : ℂ → ℂ) (z : ℂ) :
    (∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧
      (fun s => finitePerturbedZeta e r s-p s) =ᶠ[𝓝[≠] z] g) ↔
    (∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧
      (fun s => riemannZeta s-p s) =ᶠ[𝓝[≠] z] g) := by
  have hc := (finite_zeta_correction_entire e r).analyticAt z
  constructor
  · rintro ⟨g,hg,he⟩
    refine ⟨fun s => g s-finiteZetaCorrection e r s,hg.sub hc,?_⟩
    filter_upwards [he] with s hs
    dsimp [finitePerturbedZeta] at hs ⊢
    rw [← hs]
    ring
  · rintro ⟨g,hg,he⟩
    refine ⟨fun s => g s+finiteZetaCorrection e r s,hg.add hc,?_⟩
    filter_upwards [he] with s hs
    dsimp [finitePerturbedZeta] at hs ⊢
    rw [← hs]
    ring

theorem finite_perturbed_zeta_regular_iff {N : ℕ} (e : Fin N ↪ ℕ)
    (r : Fin N → ℝ) (s : ℂ) :
    DifferentiableAt ℂ (finitePerturbedZeta e r) s ↔ s ≠ 1 := by
  constructor
  · intro hd hs
    subst s
    have hc : ContinuousAt (fun s : ℂ => (s-1)*finitePerturbedZeta e r s) 1 :=
      (continuousAt_id.sub continuousAt_const).mul hd.continuousAt
    have hz : Tendsto (fun s : ℂ => (s-1)*finitePerturbedZeta e r s)
        (𝓝[≠] 1) (𝓝 0) := by
      simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {1}ᶜ))
    exact zero_ne_one (tendsto_nhds_unique hz (finite_perturbed_zeta_residue e r))
  · exact finite_perturbed_zeta_regular e r s

end
end Sigma
