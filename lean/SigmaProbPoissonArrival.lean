import SigmaProbPoisson
import SigmaProbDeficitCDF
import Mathlib.Topology.Instances.Rat

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

/-- The actual second hitting time, using rational observation times. Infinity
is retained on paths which never reach two arrivals. -/
def poissonSecondArrival {Ω : Type*} (N : ℝ → Ω → ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨅ q : ℚ, if 0 ≤ (q : ℝ) ∧ 2 ≤ N q ω then ENNReal.ofReal q else ⊤

theorem poisson_second_arrival_measurable {Ω : Type*} [MeasurableSpace Ω]
    (N : ℝ → Ω → ℕ) (hN : ∀ t, Measurable (N t)) : Measurable (poissonSecondArrival N) := by
  apply Measurable.iInf
  intro q
  exact Measurable.ite ((MeasurableSet.const _).inter (measurableSet_le measurable_const (hN q)))
    measurable_const measurable_const

/-- For a nondecreasing path, reaching two by t bounds the rational hitting
time by t. No right-continuity assumption is needed for this direction. -/
theorem poisson_second_arrival_le_of_count {Ω : Type*} (N : ℝ → Ω → ℕ) (ω : Ω)
    (hm : Monotone (fun t => N t ω)) (t : ℝ) (ht : 0 ≤ t) (hcount : 2 ≤ N t ω) :
    poissonSecondArrival N ω ≤ ENNReal.ofReal t := by
  have hb (s : ℝ) (hs : t < s) : poissonSecondArrival N ω ≤ ENNReal.ofReal s := by
    obtain ⟨q, htq, hqs⟩ := exists_rat_btwn hs
    have hq : 0 ≤ (q : ℝ) ∧ 2 ≤ N q ω := ⟨ht.trans htq.le, hcount.trans (hm htq.le)⟩
    exact (iInf_le_of_le q (by rw [if_pos hq])).trans (ENNReal.ofReal_le_ofReal hqs.le)
  exact ge_of_tendsto (ENNReal.continuous_ofReal.continuousAt.tendsto.mono_left
    inf_le_left : Tendsto ENNReal.ofReal (𝓝[>] t) (𝓝 (ENNReal.ofReal t)))
    (eventually_mem_nhdsWithin.mono hb)

/-- The elementary event identity for the second arrival. Local constancy on
the right is the discrete-valued form of right continuity. -/
theorem poisson_second_arrival_tail_iff {Ω : Type*} (N : ℝ → Ω → ℕ) (ω : Ω)
    (hm : Monotone (fun t => N t ω)) (t : ℝ) (ht : 0 ≤ t)
    (hr : ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Icc t (t+ε), N s ω = N t ω) :
    ENNReal.ofReal t < poissonSecondArrival N ω ↔ N t ω ≤ 1 := by
  constructor
  · intro h
    by_contra hn
    have hc : 2 ≤ N t ω := by omega
    exact (not_le_of_gt h) (poisson_second_arrival_le_of_count N ω hm t ht hc)
  · intro hc
    obtain ⟨ε, hε, hr⟩ := hr
    have hb : ENNReal.ofReal (t+ε) ≤ poissonSecondArrival N ω := by
      apply le_iInf
      intro q
      split_ifs with hq
      · apply ENNReal.ofReal_le_ofReal
        by_contra hlt
        have hqt : (q : ℝ) < t+ε := lt_of_not_ge hlt
        by_cases hqt' : (q : ℝ) ≤ t
        · have hmono : N q ω ≤ N t ω := hm hqt'
          omega
        · have he := hr q ⟨le_of_lt (lt_of_not_ge hqt'), hqt.le⟩
          omega
      · exact le_top
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < t+ε)).mpr (by linarith) |>.trans_le hb

theorem poisson_mass_at_most_one (t : ℝ≥0) :
    poissonMeasure t {n : ℕ | n ≤ 1} = ENNReal.ofReal ((1+(t : ℝ))*Real.exp (-t)) := by
  have he : {n : ℕ | n ≤ 1} = {0,1} := by
    ext n
    simp only [mem_setOf_eq, mem_insert_iff, mem_singleton_iff]
    omega
  rw [he, show ({0,1} : Set ℕ) = {0} ∪ {1} by rfl,
    measure_union (by simp) (measurableSet_singleton 1)]
  rw [poissonMeasure,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton 0),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton 1)]
  change ENNReal.ofReal (poissonPMFReal t 0) + ENNReal.ofReal (poissonPMFReal t 1) = _
  simp only [poissonPMFReal,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, pow_zero, pow_one,
    mul_one, div_one]
  rw [← ENNReal.ofReal_add (Real.exp_pos _).le]
  · congr 1
    ring
  · positivity

/-- The literal second-hitting-time tail of a measurable counting process with
Poisson marginals. This theorem does not assert process existence. -/
theorem poisson_second_arrival_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (N : ℝ → Ω → ℕ) (hN : ∀ t, Measurable (N t))
    (hm : ∀ ω, Monotone (fun t => N t ω))
    (hr : ∀ ω t, 0 ≤ t → ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Icc t (t+ε), N s ω = N t ω)
    (hlaw : ∀ t : ℝ≥0, μ.map (N t) = poissonMeasure t) (t : ℝ) (ht : 0 ≤ t) :
    μ {ω | ENNReal.ofReal t < poissonSecondArrival N ω} =
      ENNReal.ofReal (gammaSurvival t) := by
  have he : {ω | ENNReal.ofReal t < poissonSecondArrival N ω} =
      (N t) ⁻¹' {n : ℕ | n ≤ 1} := by
    ext ω
    exact poisson_second_arrival_tail_iff N ω (hm ω) t ht (hr ω t ht)
  have hl : μ.map (N t) = poissonMeasure ⟨t, ht⟩ := hlaw ⟨t, ht⟩
  rw [he, ← Measure.map_apply (hN t) (Set.to_countable _).measurableSet,
    hl, poisson_mass_at_most_one]
  rfl

theorem nat_path_right_continuous_local_const (f : ℝ → ℕ) (t : ℝ)
    (hc : ContinuousWithinAt f (Ici t) t) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Icc t (t+ε), f s = f t := by
  have he : ∀ᶠ s in 𝓝[≥] t, f s = f t :=
    hc ((isOpen_discrete _).mem_nhds (show f t ∈ ({f t} : Set ℕ) from rfl))
  obtain ⟨b, hb, hsub⟩ := (nhdsWithin_Ici_basis t).mem_iff.mp he
  refine ⟨(b-t)/2, by linarith, ?_⟩
  intro s hs
  exact hsub ⟨hs.1, by have := hs.2; linarith⟩

/-- Finiteness of the second hitting time is a consequence of Poisson
marginals; it is not imposed as a path hypothesis. -/
theorem poisson_second_arrival_finite_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (N : ℝ → Ω → ℕ) (hN : ∀ t, Measurable (N t))
    (hm : ∀ ω, Monotone (fun t => N t ω))
    (hr : ∀ ω t, 0 ≤ t → ContinuousWithinAt (fun s => N s ω) (Ici t) t)
    (hlaw : ∀ t : ℝ≥0, μ.map (N t) = poissonMeasure t) :
    ∀ᵐ ω ∂μ, poissonSecondArrival N ω ≠ ⊤ := by
  have hb (n : ℕ) : μ {ω | poissonSecondArrival N ω = ⊤} ≤
      ENNReal.ofReal (gammaSurvival n) := by
    rw [← poisson_second_arrival_tail μ N hN hm
      (fun ω t ht => nat_path_right_continuous_local_const _ t (hr ω t ht)) hlaw n (Nat.cast_nonneg n)]
    apply measure_mono
    intro ω hω
    change poissonSecondArrival N ω = ⊤ at hω
    simp [hω]
  have hl : Tendsto (fun n : ℕ => ENNReal.ofReal (gammaSurvival n)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal
      (gamma_survival_tendsto.comp tendsto_natCast_atTop_atTop)
  have hz : μ {ω | poissonSecondArrival N ω = ⊤} = 0 :=
    le_antisymm (ge_of_tendsto hl (Eventually.of_forall hb)) bot_le
  apply ae_iff.mpr
  simpa only [not_not] using hz

theorem poisson_second_arrival_real_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (N : ℝ → Ω → ℕ) (hN : ∀ t, Measurable (N t))
    (hm : ∀ ω, Monotone (fun t => N t ω))
    (hr : ∀ ω t, 0 ≤ t → ContinuousWithinAt (fun s => N s ω) (Ici t) t)
    (hlaw : ∀ t : ℝ≥0, μ.map (N t) = poissonMeasure t) (t : ℝ) (ht : 0 ≤ t) :
    (μ.map (fun ω => (poissonSecondArrival N ω).toReal)) (Ioi t) =
      ENNReal.ofReal (gammaSurvival t) := by
  rw [Measure.map_apply (poisson_second_arrival_measurable N hN).ennreal_toReal measurableSet_Ioi]
  rw [← poisson_second_arrival_tail μ N hN hm
    (fun ω t ht => nat_path_right_continuous_local_const _ t (hr ω t ht)) hlaw t ht]
  apply measure_congr
  filter_upwards [poisson_second_arrival_finite_ae μ N hN hm hr hlaw] with ω hω
  exact propext (ENNReal.ofReal_lt_iff_lt_toReal ht hω).symm

/-- The actual probability law of the second arrival is Gamma(2,1). All
measurability, finiteness and endpoint cases of the hitting time are derived.
This is a supplied-process theorem; construction of that process is separate. -/
theorem poisson_second_arrival_gamma_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℝ → Ω → ℕ) (hN : ∀ t, Measurable (N t))
    (hm : ∀ ω, Monotone (fun t => N t ω))
    (hr : ∀ ω t, 0 ≤ t → ContinuousWithinAt (fun s => N s ω) (Ici t) t)
    (hlaw : ∀ t : ℝ≥0, μ.map (N t) = poissonMeasure t) :
    μ.map (fun ω => (poissonSecondArrival N ω).toReal) = gammaProbability := by
  let T : Ω → ℝ := fun ω => (poissonSecondArrival N ω).toReal
  have hT : Measurable T := (poisson_second_arrival_measurable N hN).ennreal_toReal
  letI : IsProbabilityMeasure (μ.map T) := isProbabilityMeasure_map hT.aemeasurable
  have htail (t : ℝ) : μ.map T (Ioi t) = gammaProbability (Ioi t) := by
    by_cases ht : 0 ≤ t
    · rw [poisson_second_arrival_real_tail μ N hN hm hr hlaw t ht,
        gamma_probability_tail t ht]
    · have hpre : T ⁻¹' Ioi t = univ := by
        ext ω
        simp only [mem_preimage, mem_Ioi, mem_univ, iff_true]
        exact (lt_of_not_ge ht).trans_le ENNReal.toReal_nonneg
      rw [Measure.map_apply hT measurableSet_Ioi, hpre, measure_univ]
      apply le_antisymm
      · have h0 : gammaProbability (Ioi 0) = 1 := by
          simpa [gammaSurvival] using gamma_probability_tail 0 (le_refl 0)
        rw [← h0]
        exact measure_mono (Ioi_subset_Ioi (le_of_not_ge ht))
      · exact prob_le_one
  apply Measure.ext_of_Iic
  intro t
  rw [← compl_Ioi, measure_compl measurableSet_Ioi (measure_ne_top _ _),
    measure_compl measurableSet_Ioi (measure_ne_top _ _), htail, measure_univ, measure_univ]

end
end Sigma
