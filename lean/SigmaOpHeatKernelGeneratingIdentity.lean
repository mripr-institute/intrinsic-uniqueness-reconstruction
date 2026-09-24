import SigmaOpHeatKernelHilbert

namespace Sigma
noncomputable section
open MeasureTheory Filter ProbabilityTheory
open scoped BigOperators Topology
set_option maxHeartbeats 6000000

private theorem generating_basis_term {q : ℝ} (hq : 0 ≤ q) (hq' : q < 1/4)
    (n : ℕ) :
    (laguerreHilbertBasis.repr (laguerreGeneratingVector q hq hq') n) •
      laguerreHilbertBasis n =
      (q : ℂ)^n • laguerreL2Vector n := by
  rw [laguerre_generating_vector_coordinate hq hq' n,
    laguerre_hilbert_basis_apply, normalizedLaguerreL2Vector, smul_smul]
  have hn : Real.sqrt (n+1) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  congr 1
  have hquot : (n+1:ℝ)/Real.sqrt (n+1) = Real.sqrt (n+1) := by
    rw [div_eq_iff hn]
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (n+1:ℝ))]
  rw [hquot]
  have hnc : (Real.sqrt (n+1) : ℂ) ≠ 0 := by exact_mod_cast hn
  calc
    _ = (q : ℂ)^n * ((Real.sqrt (n+1) : ℂ) * (Real.sqrt (n+1) : ℂ)⁻¹) := by ring
    _ = (q : ℂ)^n := by rw [mul_inv_cancel₀ hnc, mul_one]

private theorem generating_partial_sum_coe_ae (q : ℝ) (N : ℕ) :
    ((∑ n ∈ Finset.range N, (q : ℂ)^n • laguerreL2Vector n :
      LaguerreWeightedHilbert) : ℝ → ℂ) =ᵐ[gammaProbability]
      fun x => (∑ n ∈ Finset.range N, q^n * opLaguerre n x : ℝ) := by
  induction N with
  | zero =>
      simp only [Finset.sum_range_zero]
      exact Filter.Eventually.of_forall (fun x => by simp)
  | succ N ih =>
      simp only [Finset.sum_range_succ]
      have hadd := Lp.coeFn_add
        (∑ n ∈ Finset.range N, (q : ℂ)^n • laguerreL2Vector n)
        ((q : ℂ)^N • laguerreL2Vector N)
      have hsmul := Lp.coeFn_smul ((q : ℂ)^N) (laguerreL2Vector N)
      have hterm := (op_laguerre_complex_mem_l2 N).coeFn_toLp
      filter_upwards [hadd, hsmul, ih, hterm] with x h₁ h₂ h₃ h₄
      change laguerreL2Vector N x = _ at h₄
      rw [h₁, Pi.add_apply, h₂, h₃]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [h₄]
      simp [Complex.ofReal_pow, Complex.ofReal_mul, smul_eq_mul]

/-- The Gamma-weighted `L²` Laguerre expansion of the literal generating
function has its pointwise power series as an almost-everywhere representative. -/
theorem laguerre_generating_function_eq_tsum_ae {q : ℝ}
    (hq : 0 < q) (hq' : q < 1/4) :
    (fun x : ℝ => (laguerreGeneratingFunction q x : ℂ)) =ᵐ[gammaProbability]
      (fun x => (∑' n : ℕ, q^n * opLaguerre n x : ℝ)) := by
  let v := laguerreGeneratingVector q hq.le hq'
  let S : ℕ → LaguerreWeightedHilbert := fun N =>
    ∑ n ∈ Finset.range N, (q : ℂ)^n • laguerreL2Vector n
  let f : ℕ → ℝ → ℂ := fun N x =>
    (∑ n ∈ Finset.range N, q^n * opLaguerre n x : ℝ)
  let g : ℝ → ℂ := fun x => (∑' n : ℕ, q^n * opLaguerre n x : ℝ)
  have hS : Tendsto S atTop (𝓝 v) := by
    convert (laguerreHilbertBasis.hasSum_repr v).tendsto_sum_nat using 1
    funext N
    apply Finset.sum_congr rfl
    intro n hn
    exact (generating_basis_term hq.le hq' n).symm
  have hmeasure := tendstoInMeasure_of_tendsto_Lp hS
  obtain ⟨ns, hns, hae⟩ := hmeasure.exists_seq_tendsto_ae
  have hrepr : ∀ᵐ x : ℝ ∂gammaProbability, ∀ N : ℕ, S N x = f N x := by
    rw [ae_all_iff]
    intro N
    exact generating_partial_sum_coe_ae q N
  have hpositive : ∀ᵐ x : ℝ ∂gammaProbability, 0 < x := by
    have hn : ∀ᵐ x : ℝ ∂gammaProbability, 0 ≤ x := by
      simpa only [ae_iff, not_le] using gamma_probability_negative_ray
    have hne : ∀ᵐ x : ℝ ∂gammaProbability, x ≠ 0 := by
      rw [ae_iff]
      simpa only [not_ne_iff, Set.setOf_eq_eq_singleton] using
        gamma_probability_no_atom 0
    filter_upwards [hn, hne] with x hx hxn
    exact lt_of_le_of_ne hx (Ne.symm hxn)
  have hv : (v : ℝ → ℂ) =ᵐ[gammaProbability]
      fun x => (laguerreGeneratingFunction q x : ℂ) :=
    (laguerre_generating_function_mem_l2 hq.le hq').coeFn_toLp
  filter_upwards [hae, hrepr, hpositive, hv] with x hx hrep hxpos hfun
  have hpoint : Tendsto (fun N => f N x) atTop (𝓝 (g x)) :=
    ((laguerre_generating_series_uniform_on_box hq
      (lt_trans hq' (by norm_num : (1/4:ℝ) < 1)) hxpos.le).tendsto_at
      ⟨hxpos.le, le_rfl⟩).ofReal
  have hsubseq : Tendsto ns atTop atTop := hns.tendsto_atTop
  have hpoint' : Tendsto (fun i => f (ns i) x) atTop (𝓝 (g x)) :=
    hpoint.comp hsubseq
  have hrewrite : (fun i => S (ns i) x) = fun i => f (ns i) x := by
    funext i
    exact hrep (ns i)
  rw [hrewrite] at hx
  exact hfun.symm.trans (tendsto_nhds_unique hx hpoint')

/-- Local uniform convergence of the Laguerre generating series on the
positive ray. -/
theorem laguerre_generating_series_locally_uniform {q : ℝ}
    (hq : 0 < q) (hq' : q < 1) :
    TendstoLocallyUniformlyOn
      (fun N : ℕ => fun x : ℝ =>
        ∑ n ∈ Finset.range N, q^n * opLaguerre n x)
      (fun x : ℝ => ∑' n : ℕ, q^n * opLaguerre n x)
      atTop (Set.Ioi 0) := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_Ioi).2
  intro K hK hcompact
  obtain ⟨M, hM⟩ := hcompact.bddAbove
  have hsub : K ⊆ Set.Icc (0:ℝ) (max 0 M) := by
    intro x hx
    exact ⟨(hK hx).le, le_trans (hM hx) (le_max_right _ _)⟩
  exact (laguerre_generating_series_uniform_on_box hq hq' (le_max_left _ _)).mono hsub

/-- The literal paper generating function is the Laguerre power series at
every positive argument. -/
theorem laguerre_generating_function_eq_tsum {q x : ℝ}
    (hq : 0 < q) (hq' : q < 1/4) (hx : 0 < x) :
    laguerreGeneratingFunction q x =
      ∑' n : ℕ, q^n * opLaguerre n x := by
  let f : ℝ → ℂ := fun x => (laguerreGeneratingFunction q x : ℂ)
  let g : ℝ → ℂ := fun x => (∑' n : ℕ, q^n * opLaguerre n x : ℝ)
  have hgcont : ContinuousOn g (Set.Ioi (0:ℝ)) := by
    have hlim := laguerre_generating_series_locally_uniform hq
      (lt_trans hq' (by norm_num : (1/4:ℝ) < 1))
    have hterms : ∀ N : ℕ, Continuous
        (fun x : ℝ => ∑ n ∈ Finset.range N, q^n * opLaguerre n x) := by
      intro N
      apply continuous_finset_sum
      intro n hn
      have hl : Continuous (opLaguerre n) := by
        convert (opLaguerrePolynomial n).continuous using 1
        funext x
        exact (op_laguerre_polynomial_eval n x).symm
      exact continuous_const.mul hl
    have hc := hlim.continuousOn
      (Filter.Eventually.of_forall (fun N => (hterms N).continuousOn))
    exact Complex.continuous_ofReal.continuousOn.comp hc (Set.mapsTo_univ _ _)
  have hfcont : ContinuousOn f (Set.Ioi (0:ℝ)) := by
    have hc : Continuous (fun x => laguerreGeneratingFunction q x) := by
      unfold laguerreGeneratingFunction
      fun_prop
    exact (Complex.continuous_ofReal.comp hc).continuousOn
  have hAC : (volume.restrict (Set.Ioi (0:ℝ)) : Measure ℝ) ≪ gammaProbability := by
    have hpos : ∀ᵐ y : ℝ ∂(volume.restrict (Set.Ioi (0:ℝ)) : Measure ℝ),
        gammaPDF 2 1 y ≠ 0 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact (ENNReal.ofReal_pos.mpr
        (gammaPDFReal_pos (by norm_num) (by norm_num) hy)).ne'
    have hmeas : Measurable (gammaPDF 2 1) := by
      simpa only [gammaPDF] using (measurable_gammaPDFReal 2 1).ennreal_ofReal
    have hm := withDensity_absolutelyContinuous'
      hmeas.aemeasurable.restrict hpos
    rw [← restrict_withDensity measurableSet_Ioi] at hm
    exact hm.trans (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have heq : f =ᵐ[(volume.restrict (Set.Ioi (0:ℝ)) : Measure ℝ)] g :=
    hAC.ae_le (laguerre_generating_function_eq_tsum_ae hq hq')
  have hevery := Measure.eqOn_open_of_ae_eq heq isOpen_Ioi hfcont hgcont
  have hc := hevery hx
  exact Complex.ofReal_injective hc

end
end Sigma
