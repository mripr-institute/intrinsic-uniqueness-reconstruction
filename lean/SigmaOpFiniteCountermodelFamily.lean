import SigmaOpFiniteCountermodelLocal
import SigmaOpFiniteCountermodelSpectrum

namespace Sigma
noncomputable section
open Filter
open scoped Topology BigOperators

/-- Geometrically spaced positions in the original integer spectrum. Their
shifted eigenvalues are `2^(j+1)`, so the constraint Jacobian is Vandermonde. -/
def finiteGeometricIndex (N : ℕ) : Fin N ↪ ℕ where
  toFun j := 2^(j.val+1)-1
  inj' := by
    intro i j h
    change 2^(i.val+1)-1 = 2^(j.val+1)-1 at h
    have hi : 1 ≤ (2 : ℕ)^(i.val+1) := one_le_pow₀ (by norm_num)
    have hj : 1 ≤ (2 : ℕ)^(j.val+1) := one_le_pow₀ (by norm_num)
    have hp : 2^(i.val+1) = 2^(j.val+1) := by omega
    have hv := (pow_right_strictMono₀ (by norm_num : 1 < (2 : ℕ))).injective hp
    exact Fin.ext (by omega)

theorem finite_geometric_index_positive (N : ℕ) (j : Fin N) :
    0 < finiteGeometricIndex N j := by
  change 0 < 2^(j.val+1)-1
  exact Nat.sub_pos_of_lt (one_lt_pow₀ (by norm_num : 1 < (2 : ℕ)) (by omega))

theorem finite_geometric_index_shift (N : ℕ) (j : Fin N) :
    ((finiteGeometricIndex N j : ℕ) : ℝ)+1 = (2 : ℝ)^(j.val+1) := by
  have hp : 1 ≤ (2 : ℕ)^(j.val+1) := one_le_pow₀ (by norm_num)
  change ((2^(j.val+1)-1 : ℕ) : ℝ)+1 = _
  rw [Nat.cast_sub hp]
  push_cast
  ring

theorem finite_invariant_base_exp (N : ℕ) (j : Fin N) :
    Real.exp (finiteInvariantBase N j) =
      ((finiteGeometricIndex N j : ℕ) : ℝ)+1 := by
  rw [finite_geometric_index_shift]
  simpa [finiteInvariantBase,Real.exp_log (by norm_num : (0 : ℝ)<2)] using
    Real.exp_nat_mul (Real.log 2) (j.val+1)

/-- The local level curve converted back from logarithmic coordinates. Each
coordinate remains in a disjoint interval around its original integer. -/
theorem finite_exponential_preserving_curve {n : ℕ} (a : Fin n → ℝ)
    (ha : Function.Injective a) :
    ∃ r : ℝ → (Fin (n+1) → ℝ),
      (∀ j, r 0 j = ((finiteGeometricIndex (n+1) j : ℕ) : ℝ)+1) ∧
      ContinuousAt r 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ),
        (∀ j, |r t j-(((finiteGeometricIndex (n+1) j : ℕ) : ℝ)+1)| < 1/4) ∧
        (∀ i : Fin n, (∑ j, finiteInvariantPrimitive (a i) (Real.log (r t j))) =
          ∑ j, finiteInvariantPrimitive (a i)
            (Real.log (((finiteGeometricIndex (n+1) j : ℕ) : ℝ)+1))) ∧
        (t ≠ 0 → ∃ j, r t j ≠ ((finiteGeometricIndex (n+1) j : ℕ) : ℝ)+1) ∧
        ContinuousAt r t) := by
  obtain ⟨γ,h0,hc,hγ⟩ := finite_invariant_preserving_curve a ha
  let r : ℝ → (Fin (n+1) → ℝ) := fun t j => Real.exp (γ t j)
  have hr0 (j) : r 0 j = ((finiteGeometricIndex (n+1) j : ℕ) : ℝ)+1 := by
    dsimp [r]
    rw [h0,finite_invariant_base_exp]
  have hrc : ContinuousAt r 0 := continuousAt_pi.mpr fun j =>
    Real.continuous_exp.continuousAt.comp ((continuous_apply j).continuousAt.comp hc)
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ j,
      |r t j-(((finiteGeometricIndex (n+1) j : ℕ) : ℝ)+1)| < 1/4 := by
    apply eventually_all.mpr
    intro j
    have hcont : ContinuousAt (fun t => |r t j-r 0 j|) 0 :=
      (((continuous_apply j).continuousAt.comp hrc).sub continuousAt_const).abs
    have hlt : |r 0 j-r 0 j| < (1 : ℝ)/4 := by norm_num
    simpa [hr0] using hcont.eventually_lt continuousAt_const hlt
  refine ⟨r,hr0,hrc,?_⟩
  filter_upwards [hnear,hγ] with t hnt hgt
  refine ⟨hnt,?_,?_,?_⟩
  · intro i
    have hlog (j) : Real.log (((finiteGeometricIndex (n+1) j : ℕ) : ℝ)+1) =
        finiteInvariantBase (n+1) j := by
      rw [← finite_invariant_base_exp,Real.log_exp]
    simpa [r,Real.log_exp,hlog] using hgt.1 i
  · intro ht
    by_contra h
    push_neg at h
    apply hgt.2.1 ht
    funext j
    apply Real.exp_injective
    rw [finite_invariant_base_exp]
    exact h j
  · exact continuousAt_pi.mpr fun j => Real.continuous_exp.continuousAt.comp
      ((continuous_apply j).continuousAt.comp hgt.2.2)

theorem finite_primitive_sum_exp {N : ℕ} (a : ℝ) (x y : Fin N → ℝ)
    (ha : a ≠ 0)
    (h : (∑ j,finiteInvariantPrimitive a (x j)) =
      ∑ j,finiteInvariantPrimitive a (y j)) :
    (∑ j,Real.exp (a*x j)) = ∑ j,Real.exp (a*y j) := by
  simp only [finiteInvariantPrimitive,ha,if_false,← Finset.sum_div] at h
  exact (div_left_inj' ha).mp h

theorem finite_near_integer_changed (k : ℕ) (r : ℝ)
    (hnear : |r-((k : ℝ)+1)| < 1/4) (hne : r ≠ (k : ℝ)+1) :
    ∀ m : ℕ, r-1 ≠ (m : ℝ) := by
  intro m hm
  obtain ⟨hl,hu⟩ := abs_lt.mp hnear
  have hmle : m ≤ k := Nat.lt_succ_iff.mp (by
    exact_mod_cast (show (m : ℝ) < (k : ℝ)+1 by linarith))
  have hkle : k ≤ m := Nat.lt_succ_iff.mp (by
    exact_mod_cast (show (k : ℝ) < (m : ℝ)+1 by linarith))
  have he := Nat.le_antisymm hmle hkle
  subst m
  exact hne (by linarith)

/-- A moved coordinate in its disjoint integer neighborhood gives an actual
new spectral value, so the deformation cannot be a permutation. -/
theorem finite_perturbed_spectrum_changed {N : ℕ} (e : Fin N ↪ ℕ)
    (r : Fin N → ℝ) (j : Fin N)
    (hnear : |r j-((e j : ℝ)+1)| < 1/4) (hne : r j ≠ (e j : ℝ)+1) :
    ∃ z : ℂ, z ∈ unboundedOperatorSpectrum (finitePerturbedOperator e r) ∧
      z ∉ unboundedOperatorSpectrum (laguerreSpectralOperator id) := by
  let z : ℂ := ((r j-1 : ℝ) : ℂ)
  refine ⟨z,?_,?_⟩
  · intro hR
    apply laguerreHilbertBasis.orthonormal.ne_zero (e j)
    apply bounded_unbounded_resolvent_excludes_eigenvalue _ z hR
      ⟨laguerreHilbertBasis (e j),laguerre_basis_mem_spectral_domain _ (e j)⟩
    simpa [z,finite_shifted_spectrum_selected] using
      finite_perturbed_operator_basis_action e r (e j)
  · rw [laguerre_full_spectrum_exact]
    rintro ⟨m,hm⟩
    have hm' : r j-1 = (m : ℝ) := by
      simpa [z] using (congrArg Complex.re hm).symm
    exact finite_near_integer_changed (e j) (r j) hnear hne m hm'

/-- Finite familiar zeta data do not determine the spectrum. We preserve the
finite part at one and the zeta determinant simultaneously, so either may be
omitted from the requested finite list. The construction starts at the original
operator and changes only finitely many strictly positive eigenvalues. -/
theorem finite_spectral_invariant_countermodels (S : Finset ℝ) :
    ∃ (N : ℕ) (e : Fin N ↪ ℕ) (r : ℝ → Fin N → ℝ),
      (∀ j, 0 < e j) ∧
      finitePerturbedOperator e (r 0) = laguerreSpectralOperator id ∧
      ContinuousAt r 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ),
        ContinuousAt r t ∧
        (∀ j, 1 < r t j) ∧
        IsSelfAdjoint (finitePerturbedOperator e (r t)) ∧
        (∀ x : (finitePerturbedOperator e (r t)).domain,
          0 ≤ (@inner ℂ LaguerreWeightedHilbert _ x.val
            (finitePerturbedOperator e (r t) x)).re) ∧
        (∀ s ∈ S, finitePerturbedZeta e (r t) (s : ℂ) = riemannZeta (s : ℂ)) ∧
        finiteZetaCorrection e (r t) 1 = 0 ∧
        finitePerturbedZetaDeterminant e (r t) = laguerreZetaDeterminant 1 ∧
        (t ≠ 0 → ∃ z : ℂ,
          z ∈ unboundedOperatorSpectrum (finitePerturbedOperator e (r t)) ∧
          z ∉ unboundedOperatorSpectrum (laguerreSpectralOperator id))) := by
  classical
  let T : Finset ℝ := insert 0 ((insert 1 S).image Neg.neg)
  let a : Fin T.card → ℝ := fun i => (T.equivFin.symm i).val
  have ha : Function.Injective a :=
    Subtype.val_injective.comp T.equivFin.symm.injective
  have hae (v : ℝ) (hv : v ∈ T) : ∃ i, a i = v := by
    refine ⟨T.equivFin ⟨v,hv⟩,?_⟩
    simp [a]
  obtain ⟨r,hr0,hrc,hr⟩ := finite_exponential_preserving_curve a ha
  let e := finiteGeometricIndex (T.card+1)
  have h0 : finitePerturbedOperator e (r 0) = laguerreSpectralOperator id := by
    have he : r 0 = fun j => (e j : ℝ)+1 := funext hr0
    rw [he,finite_perturbed_initial_operator]
  refine ⟨T.card+1,e,r,finite_geometric_index_positive _,h0,hrc,?_⟩
  filter_upwards [hr] with t ht
  obtain ⟨hnear,hpres,hchange,hcont⟩ := ht
  have hpos (j) : 1 < r t j := by
    have he : (1 : ℝ) ≤ e j := by exact_mod_cast finite_geometric_index_positive _ j
    have hl := (abs_lt.mp (hnear j)).1
    change -(1/4 : ℝ) < r t j - ((e j : ℝ)+1) at hl
    linarith
  have hsample (s : ℝ) (hs : s ∈ insert 1 S) :
      finiteZetaCorrection e (r t) (s : ℂ) = 0 := by
    by_cases hs0 : s = 0
    · subst s
      exact finite_zeta_correction_zero e (r t)
    obtain ⟨i,hi⟩ := hae (-s) (by
      apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨s,hs,rfl⟩)
    have hp := hpres i
    rw [hi] at hp
    have he := finite_primitive_sum_exp (-s) _ _ (neg_ne_zero.mpr hs0) hp
    rw [finite_zeta_correction_real,he,sub_self,Complex.ofReal_zero]
  have hlogs : (∑ j,Real.log (r t j)) = ∑ j,Real.log ((e j : ℝ)+1) := by
    obtain ⟨i,hi⟩ := hae 0 (Finset.mem_insert_self _ _)
    have hp := hpres i
    simpa [hi,finiteInvariantPrimitive] using hp
  refine ⟨hcont,hpos,finite_perturbed_operator_selfadjoint e (r t),
    finite_perturbed_operator_nonnegative e (r t) (fun j => (hpos j).le),?_,
    ?_,finite_perturbed_determinant_preserved e (r t) hlogs,?_⟩
  · intro s hs
    simp only [finitePerturbedZeta,hsample s (Finset.mem_insert_of_mem hs),add_zero]
  · exact hsample 1 (Finset.mem_insert_self _ _)
  · intro ht0
    obtain ⟨j,hj⟩ := hchange ht0
    exact finite_perturbed_spectrum_changed e (r t) j (hnear j) hj

end
end Sigma
