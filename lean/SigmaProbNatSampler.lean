import SigmaProbPoissonClock
import SigmaProbPoisson

namespace Sigma
noncomputable section
open MeasureTheory Measure Set Filter
open scoped Topology BigOperators ENNReal

/-- Cumulative mass before the integer `n`. -/
def natPMFCumulative (q : PMF ℕ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (q k).toReal

theorem nat_pmf_cumulative_zero (q : PMF ℕ) : natPMFCumulative q 0 = 0 := by
  simp [natPMFCumulative]

theorem nat_pmf_cumulative_succ (q : PMF ℕ) (n : ℕ) :
    natPMFCumulative q (n+1) = natPMFCumulative q n+(q n).toReal := by
  exact Finset.sum_range_succ _ _

theorem nat_pmf_cumulative_mono (q : PMF ℕ) : Monotone (natPMFCumulative q) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [nat_pmf_cumulative_succ]
  exact le_add_of_nonneg_right ENNReal.toReal_nonneg

theorem nat_pmf_cumulative_bounds (q : PMF ℕ) (n : ℕ) :
    0 ≤ natPMFCumulative q n ∧ natPMFCumulative q n ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg fun k _ => ENNReal.toReal_nonneg
  · exact (sum_le_hasSum (Finset.range n) (fun _ _ => ENNReal.toReal_nonneg)
      (pmf_real_mass q))

theorem nat_pmf_cumulative_tendsto (q : PMF ℕ) :
    Tendsto (natPMFCumulative q) atTop (𝓝 1) := (pmf_real_mass q).tendsto_sum_nat

theorem nat_pmf_sample_exists (q : PMF ℕ) (z : AddCircle (1 : ℝ)) :
    ∃ n, 1-poissonCircleUniform z < natPMFCumulative q (n+1) := by
  have hu : 1-poissonCircleUniform z < 1 := by
    linarith [(poissonCircleUniform_mem z).1]
  have hh := (nat_pmf_cumulative_tendsto q).eventually
    (lt_mem_nhds hu)
  obtain ⟨n,hn⟩ := hh.exists
  exact ⟨n,hn.trans_le (nat_pmf_cumulative_mono q (Nat.le_succ n))⟩

/-- Exact inverse cumulative sampling from normalized Haar measure. Reflection
of the `(0,1]` uniform coordinate puts the quantile in `[0,1)` everywhere. -/
def natPMFSample (q : PMF ℕ) (z : AddCircle (1 : ℝ)) : ℕ :=
  Nat.find (nat_pmf_sample_exists q z)

theorem nat_pmf_sample_measurable (q : PMF ℕ) : Measurable (natPMFSample q) := by
  apply measurable_find
  intro n
  exact measurableSet_lt (measurable_const.sub poissonCircleUniform_measurable) measurable_const

theorem nat_pmf_sample_eq_iff (q : PMF ℕ) (z : AddCircle (1 : ℝ)) (n : ℕ) :
    natPMFSample q z = n ↔
      poissonCircleUniform z ∈ Ioc (1-natPMFCumulative q (n+1)) (1-natPMFCumulative q n) := by
  rw [natPMFSample,Nat.find_eq_iff]
  constructor
  · rintro ⟨hupper,hlower⟩
    refine ⟨by linarith,?_⟩
    cases n with
    | zero => simpa [nat_pmf_cumulative_zero] using (poissonCircleUniform_mem z).2
    | succ n =>
      have hn := hlower n (Nat.lt_succ_self n)
      push_neg at hn
      linarith
  · intro hz
    refine ⟨by linarith [hz.1],?_⟩
    intro k hk
    have hkn := nat_pmf_cumulative_mono q (Nat.succ_le_of_lt hk)
    have hu := hz.2
    linarith

theorem nat_pmf_sample_map (q : PMF ℕ) :
    (volume : Measure (AddCircle (1 : ℝ))).map (natPMFSample q) = q.toMeasure := by
  apply Measure.ext_of_singleton
  intro n
  rw [Measure.map_apply (nat_pmf_sample_measurable q) (measurableSet_singleton n),
    q.toMeasure_apply_singleton n (measurableSet_singleton n)]
  have he : (natPMFSample q) ⁻¹' {n} = poissonCircleUniform ⁻¹'
      Ioc (1-natPMFCumulative q (n+1)) (1-natPMFCumulative q n) := by
    ext z
    exact nat_pmf_sample_eq_iff q z n
  rw [he,← Measure.map_apply poissonCircleUniform_measurable measurableSet_Ioc,
    poissonCircleUniform_map,Measure.restrict_apply measurableSet_Ioc]
  have hsub : Ioc (1-natPMFCumulative q (n+1)) (1-natPMFCumulative q n) ⊆ Ioc (0 : ℝ) 1 := by
    intro u hu
    have hupper := (nat_pmf_cumulative_bounds q (n+1)).2
    have hlower := (nat_pmf_cumulative_bounds q n).1
    exact ⟨by linarith [hu.1],by linarith [hu.2]⟩
  rw [inter_eq_left.mpr hsub,Real.volume_Ioc,nat_pmf_cumulative_succ]
  convert ENNReal.ofReal_toReal (q.apply_ne_top n) using 1
  congr 1
  ring

end
end Sigma
