import SigmaProbPoissonClock
import SigmaProbFourier
import SigmaProbDeficitCDF
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.BorelCantelli

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

theorem poisson_exponential_clock_map (n : ℕ) :
    poissonClockProbability.map (poissonExponentialClock n) = unitExpProbability := by
  apply Measure.ext_of_Iic
  intro t
  have hu : poissonClockProbability.map
      (fun ω => poissonCircleUniform (ω n)) = volume.restrict (Ioc (0 : ℝ) 1) := by
    have hmap := Measure.map_map (μ := poissonClockProbability)
      (g := poissonCircleUniform) (f := fun ω : PoissonClockSpace => ω n)
      poissonCircleUniform_measurable (measurable_pi_apply n)
    calc
      poissonClockProbability.map (fun ω => poissonCircleUniform (ω n)) =
          (poissonClockProbability.map (fun ω : PoissonClockSpace => ω n)).map poissonCircleUniform := by
            simpa only [Function.comp_def] using hmap.symm
      _ = volume.restrict (Ioc (0 : ℝ) 1) := by
        rw [poissonClockCoordinate_map, poissonCircleUniform_map]
  have hm : Measurable (fun u : ℝ => -Real.log u) := Real.measurable_log.neg
  have hlogmap :
      (poissonClockProbability.map (fun ω : PoissonClockSpace => poissonCircleUniform (ω n))).map
          (fun u : ℝ => -Real.log u) =
        poissonClockProbability.map (poissonExponentialClock n) := by
    simpa only [poissonExponentialClock, Function.comp_def] using
      (Measure.map_map (μ := poissonClockProbability)
        (g := fun u : ℝ => -Real.log u)
        (f := fun ω : PoissonClockSpace => poissonCircleUniform (ω n)) hm
        (poissonCircleUniform_measurable.comp (measurable_pi_apply n)))
  rw [← hlogmap, hu, Measure.map_apply hm measurableSet_Iic]
  rw [Measure.restrict_apply (hm measurableSet_Iic)]
  by_cases ht : 0 ≤ t
  · have hpre : (fun u : ℝ => -Real.log u) ⁻¹' Iic t ∩ Ioc (0 : ℝ) 1 =
        Icc (Real.exp (-t)) 1 := by
      ext u
      simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioc, mem_Icc]
      constructor
      · rintro ⟨hu, ⟨hu0, hu1⟩⟩
        refine ⟨?_, hu1⟩
        have hlog : -t ≤ Real.log u := by linarith
        have h := Real.exp_le_exp.mpr hlog
        simpa [Real.exp_log hu0] using h
      · rintro ⟨hu0, hu1⟩
        refine ⟨?_, ⟨lt_of_lt_of_le (Real.exp_pos (-t)) hu0, hu1⟩⟩
        have hlog := Real.log_le_log (Real.exp_pos (-t)) hu0
        rw [Real.log_exp] at hlog
        linarith
    rw [hpre, Real.volume_Icc]
    change ENNReal.ofReal (1 - Real.exp (-t)) = unitExpProbability (Iic t)
    rw [← ProbabilityTheory.ofReal_cdf unitExpProbability t]
    change ENNReal.ofReal (1 - Real.exp (-t)) =
      ENNReal.ofReal (ProbabilityTheory.exponentialCDFReal 1 t)
    rw [ProbabilityTheory.exponentialCDFReal_eq (by norm_num) t]
    simp [ht]
  · have hpre : (fun u : ℝ => -Real.log u) ⁻¹' Iic t ∩ Ioc (0 : ℝ) 1 = ∅ := by
      ext u
      simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioc, mem_empty_iff_false]
      constructor
      · rintro ⟨hu, ⟨hu0, hu1⟩⟩
        have hlog := Real.log_nonpos hu0.le hu1
        linarith
      · intro h
        exact h.elim
    rw [hpre, measure_empty]
    change 0 = unitExpProbability (Iic t)
    rw [← ProbabilityTheory.ofReal_cdf unitExpProbability t]
    change 0 = ENNReal.ofReal (ProbabilityTheory.exponentialCDFReal 1 t)
    rw [ProbabilityTheory.exponentialCDFReal_eq (by norm_num) t]
    simp [ht]

/-- The concrete clock family has the exact i.i.d. Exp(1) law, not only a
two-variable independent-sum identity. -/
theorem poisson_unit_rate_interarrival_law :
    ProbabilityTheory.iIndepFun (fun _ : ℕ => inferInstance)
      poissonExponentialClock poissonClockProbability ∧
    ∀ n, poissonClockProbability.map (poissonExponentialClock n) = unitExpProbability :=
  ⟨poissonExponentialClocks_independent, poisson_exponential_clock_map⟩

/-- The successive waiting times in the canonical exponential-interarrival
construction are exactly the independent Exp(1) coordinates. -/
abbrev unitRatePoissonProcessInterarrival := poissonExponentialClock

theorem unit_rate_poisson_process_interarrival_law :
    ProbabilityTheory.iIndepFun (fun _ : ℕ => inferInstance)
      unitRatePoissonProcessInterarrival poissonClockProbability ∧
    ∀ n, poissonClockProbability.map (unitRatePoissonProcessInterarrival n) =
      unitExpProbability := by
  exact poisson_unit_rate_interarrival_law

/-- In the canonical exponential-interarrival construction, the `n`th
arrival epoch (starting with index zero) is the sum of the first `n+1`
independent unit exponential waiting times. -/
def poissonRenewalArrival (n : ℕ) (ω : PoissonClockSpace) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), unitRatePoissonProcessInterarrival i ω

/-- The canonical arrival-time form of a unit-rate Poisson process, built from
the entire infinite i.i.d. Exp(1) waiting-time sequence on the product space. -/
abbrev unitRatePoissonProcessArrival := poissonRenewalArrival

/-- The counting variable is the extended cardinality of the arrival epochs
which have occurred by time `t`, so repeated epochs (zero waiting times on
null-coordinate paths) are counted with their multiplicity. -/
def unitRatePoissonProcessCount (t : ℝ) (ω : PoissonClockSpace) : ℕ∞ :=
  {n | poissonRenewalArrival n ω ≤ t}.encard

theorem poisson_renewal_arrival_measurable (n : ℕ) :
    Measurable (poissonRenewalArrival n) := by
  unfold poissonRenewalArrival
  exact Finset.measurable_sum _ (fun i _ => poissonExponentialClock_measurable i)

theorem poisson_renewal_arrival_zero (ω : PoissonClockSpace) :
    poissonRenewalArrival 0 ω = poissonExponentialClock 0 ω := by
  simp [poissonRenewalArrival]

theorem poisson_renewal_arrival_succ (n : ℕ) (ω : PoissonClockSpace) :
    poissonRenewalArrival (n + 1) ω =
      poissonRenewalArrival n ω + poissonExponentialClock (n + 1) ω := by
  simp [poissonRenewalArrival, Finset.sum_range_succ, Nat.add_assoc]

theorem poisson_renewal_arrivals_monotone (ω : PoissonClockSpace) :
    Monotone (fun n => poissonRenewalArrival n ω) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [poisson_renewal_arrival_succ]
  exact le_add_of_nonneg_right (poissonExponentialClock_nonneg (n + 1) ω)

def poissonLongWaitingTime (n : ℕ) : Set PoissonClockSpace :=
  {ω | 1 < poissonExponentialClock n ω}

theorem unit_exp_strict_tail_one :
    unitExpProbability (Ioi (1 : ℝ)) = ENNReal.ofReal (Real.exp (-1)) := by
  have hcdf : unitExpProbability (Iic (1 : ℝ)) = ENNReal.ofReal (1-Real.exp (-1)) := by
    rw [← ProbabilityTheory.ofReal_cdf unitExpProbability 1]
    change ENNReal.ofReal (ProbabilityTheory.exponentialCDFReal 1 1) = _
    rw [ProbabilityTheory.exponentialCDFReal_eq (by norm_num) 1]
    norm_num
  have hq : 0 ≤ 1-Real.exp (-1) := by
    rw [sub_nonneg]
    exact Real.exp_le_one_iff.mpr (by norm_num)
  have hcomp : Ioi (1 : ℝ) = (Iic 1)ᶜ := by
    ext x
    simp
  rw [hcomp, measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ, hcdf]
  have hsub := ENNReal.ofReal_sub (1 : ℝ) hq
  rw [ENNReal.ofReal_one] at hsub
  calc
    1 - ENNReal.ofReal (1-Real.exp (-1)) =
        ENNReal.ofReal (1-(1-Real.exp (-1))) := hsub.symm
    _ = ENNReal.ofReal (Real.exp (-1)) := by congr 1; ring

theorem poisson_long_waiting_time_probability (n : ℕ) :
    poissonClockProbability (poissonLongWaitingTime n) =
      ENNReal.ofReal (Real.exp (-1)) := by
  change poissonClockProbability ((poissonExponentialClock n) ⁻¹' Ioi 1) = _
  rw [← Measure.map_apply (poissonExponentialClock_measurable n) measurableSet_Ioi,
    poisson_exponential_clock_map, unit_exp_strict_tail_one]

theorem poisson_long_waiting_times_independent :
    ProbabilityTheory.iIndepSet poissonLongWaitingTime poissonClockProbability := by
  change ProbabilityTheory.iIndepSet (fun n =>
    (poissonExponentialClock n) ⁻¹' Ioi (1 : ℝ)) poissonClockProbability
  rw [ProbabilityTheory.iIndepSet_iff_meas_biInter
    (fun n => (poissonExponentialClock_measurable n) measurableSet_Ioi)]
  intro s
  simpa [poissonLongWaitingTime] using
    poissonExponentialClocks_independent.measure_inter_preimage_eq_mul s
      (sets := fun _ => Ioi (1 : ℝ)) (fun _ _ => measurableSet_Ioi)

theorem poisson_long_waiting_times_sum_diverges :
    (∑' n : ℕ, poissonClockProbability (poissonLongWaitingTime n)) = ⊤ := by
  simp_rw [poisson_long_waiting_time_probability]
  exact ENNReal.tsum_const_eq_top_of_ne_zero (by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))

theorem poisson_long_waiting_times_occur_infinitely_often_ae :
    poissonClockProbability (Filter.limsup poissonLongWaitingTime atTop) = 1 :=
  ProbabilityTheory.measure_limsup_eq_one
    (fun n => (poissonExponentialClock_measurable n) measurableSet_Ioi)
    poisson_long_waiting_times_independent poisson_long_waiting_times_sum_diverges

theorem poisson_renewal_arrivals_unbounded_of_infinitely_many_long_gaps
    (ω : PoissonClockSpace) (hω : ω ∈ Filter.limsup poissonLongWaitingTime atTop) (t : ℝ) :
    ∃ n, t < poissonRenewalArrival n ω := by
  classical
  have hinf : {n : ℕ | ω ∈ poissonLongWaitingTime n}.Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro n
    have hfreq : ∃ᶠ k in atTop, ω ∈ poissonLongWaitingTime k :=
      (mem_limsup_iff_frequently_mem).mp hω
    obtain ⟨m, hmn, hmem⟩ := Filter.frequently_atTop'.mp hfreq n
    exact ⟨m, hmem, hmn⟩
  obtain ⟨m, hm⟩ := exists_nat_gt t
  obtain ⟨u, hu, hcard⟩ := hinf.exists_subset_card_eq (m+1)
  have hu_ne : u.Nonempty := Finset.card_pos.mp (by omega)
  let n := u.max' hu_ne
  have husub : (↑u : Set ℕ) ⊆ {i | i < n+1} := by
    intro i hi
    have hiu : i ∈ u := hi
    exact Nat.lt_succ_of_le (Finset.le_max' u i hiu)
  have hsum : (m+1 : ℝ) < ∑ i ∈ u, poissonExponentialClock i ω := by
    have hterm (i : ℕ) (hi : i ∈ u) : (1 : ℝ) < poissonExponentialClock i ω :=
      hu hi
    calc
      (m+1 : ℝ) = ∑ _i ∈ u, (1 : ℝ) := by simp [hcard]
      _ < ∑ i ∈ u, poissonExponentialClock i ω := Finset.sum_lt_sum_of_nonempty hu_ne hterm
  have hle : (∑ i ∈ u, poissonExponentialClock i ω) ≤ poissonRenewalArrival n ω := by
    rw [poissonRenewalArrival]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun i hi => Finset.mem_range.mpr (husub hi))
      (fun _ _ _ => poissonExponentialClock_nonneg _ _)
  have hmt : t < (m+1 : ℝ) := lt_of_lt_of_le hm (by exact_mod_cast Nat.le_succ m)
  exact ⟨n, lt_of_lt_of_le (hmt.trans hsum) hle⟩

theorem poisson_renewal_arrivals_tendsto_top_ae :
    ∀ᵐ ω ∂poissonClockProbability, Tendsto (fun n => poissonRenewalArrival n ω) atTop atTop := by
  filter_upwards [show ∀ᵐ ω ∂poissonClockProbability,
      ω ∈ Filter.limsup poissonLongWaitingTime atTop from by
        apply ae_iff.mpr
        have hm := poisson_long_waiting_times_occur_infinitely_often_ae
        have hL : MeasurableSet (Filter.limsup poissonLongWaitingTime atTop) := by
          rw [Filter.limsup_eq_iInf_iSup_of_nat]
          apply MeasurableSet.iInter
          intro n
          apply MeasurableSet.iUnion
          intro m
          apply MeasurableSet.iUnion
          intro hmn
          exact (poissonExponentialClock_measurable m) measurableSet_Ioi
        have hfinite : poissonClockProbability
            (Filter.limsup poissonLongWaitingTime atTop) ≠ ∞ := measure_ne_top _ _
        have hc := measure_compl hL hfinite
        rw [hm, measure_univ] at hc
        simpa using hc] with ω hω
  apply Filter.tendsto_atTop.2
  intro t
  obtain ⟨n, hn⟩ := poisson_renewal_arrivals_unbounded_of_infinitely_many_long_gaps ω hω t
  filter_upwards [eventually_ge_atTop n] with m hm
  exact (hn.trans_le (poisson_renewal_arrivals_monotone ω hm)).le

theorem unit_rate_poisson_count_le_iff (t : ℝ) (ω : PoissonClockSpace) (k : ℕ) :
    unitRatePoissonProcessCount t ω ≤ k ↔ t < poissonRenewalArrival k ω := by
  classical
  change {n | poissonRenewalArrival n ω ≤ t}.encard ≤ k ↔ _
  constructor
  · intro hc
    by_contra ht
    have hkt : poissonRenewalArrival k ω ≤ t := le_of_not_gt ht
    have hs : {n : ℕ | n < k + 1} ⊆ {n | poissonRenewalArrival n ω ≤ t} := by
      intro n hn
      exact (poisson_renewal_arrivals_monotone ω (Nat.le_of_lt_succ hn)).trans hkt
    have hcard : (k + 1 : ℕ∞) ≤ {n : ℕ | poissonRenewalArrival n ω ≤ t}.encard := by
      calc
        (k + 1 : ℕ∞) = {n : ℕ | n < k + 1}.encard := (Nat.encard_range _).symm
        _ ≤ {n : ℕ | poissonRenewalArrival n ω ≤ t}.encard := Set.encard_mono hs
    have hlt : (k : ℕ∞) < k + 1 := by exact_mod_cast Nat.lt_succ_self k
    exact (not_le_of_gt (hlt.trans_le hcard)) hc
  · intro ht
    apply le_trans (Set.encard_mono ?_)
    · rw [Nat.encard_range]
    · intro n hn
      by_contra hnk
      have hkn : k ≤ n := Nat.le_of_not_gt hnk
      have hnk' := poisson_renewal_arrivals_monotone ω hkn
      exact (not_le_of_gt ht) (hnk'.trans hn)

/-- At each fixed time, the extended arrival count is a measurable random
variable. Its level sets are differences of consecutive arrival-tail events. -/
theorem unit_rate_poisson_process_count_measurable (t : ℝ) :
    Measurable (unitRatePoissonProcessCount t) := by
  apply ENat.measurable_iff.mpr
  intro k
  have hle (n : ℕ) : MeasurableSet {ω | unitRatePoissonProcessCount t ω ≤ (n : ℕ∞)} := by
    have hs : {ω | unitRatePoissonProcessCount t ω ≤ (n : ℕ∞)} =
        (poissonRenewalArrival n) ⁻¹' Ioi t := by
      ext ω
      exact unit_rate_poisson_count_le_iff t ω n
    rw [hs]
    exact (poisson_renewal_arrival_measurable n) measurableSet_Ioi
  change MeasurableSet {ω | unitRatePoissonProcessCount t ω = (k : ℕ∞)}
  by_cases hk : k = 0
  · subst k
    change MeasurableSet {ω | unitRatePoissonProcessCount t ω = (0 : ℕ∞)}
    have hs : {ω | unitRatePoissonProcessCount t ω = (0 : ℕ∞)} =
        {ω | unitRatePoissonProcessCount t ω ≤ (0 : ℕ∞)} := by
      ext ω
      simp
    rw [hs]
    exact hle 0
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hs : {ω | unitRatePoissonProcessCount t ω = (k : ℕ∞)} =
        ({ω | unitRatePoissonProcessCount t ω ≤ (k : ℕ∞)}).diff
          {ω | unitRatePoissonProcessCount t ω ≤ ((k-1 : ℕ) : ℕ∞)} := by
      ext ω
      change (unitRatePoissonProcessCount t ω = (k : ℕ∞)) ↔
        (unitRatePoissonProcessCount t ω ≤ (k : ℕ∞) ∧
          ¬ unitRatePoissonProcessCount t ω ≤ ((k-1 : ℕ) : ℕ∞))
      constructor
      · intro he
        constructor
        · rw [he]
        · intro hle'
          rw [he] at hle'
          have hn : k ≤ k-1 := ENat.coe_le_coe.mp hle'
          omega
      · rintro ⟨hle', hnle'⟩
        obtain ⟨m, hm, hmk⟩ := ENat.le_coe_iff.mp hle'
        have hkm : k ≤ m := by
          by_contra hkm
          have hmle : m ≤ k-1 := by omega
          apply hnle'
          rw [hm]
          exact ENat.coe_le_coe.mpr hmle
        have hEq : m = k := Nat.le_antisymm hmk hkm
        rw [hm, hEq]
    rw [hs]
    exact (hle k).diff (hle (k-1))

/-- The constructed counting process has finitely many arrivals by every
fixed finite time almost surely. This is derived from divergence of the actual
cumulative arrival epochs. -/
theorem unit_rate_poisson_process_count_finite_ae (t : ℝ) :
    ∀ᵐ ω ∂poissonClockProbability, unitRatePoissonProcessCount t ω < ⊤ := by
  filter_upwards [poisson_renewal_arrivals_tendsto_top_ae] with ω hω
  have hEv : ∀ᶠ N : ℕ in atTop, t + 1 ≤ poissonRenewalArrival N ω :=
    (Filter.tendsto_atTop.1 hω) (t + 1)
  obtain ⟨N, hN⟩ := Filter.Eventually.exists hEv
  have hN' : t < poissonRenewalArrival N ω := by linarith [hN]
  have hbdd : BddAbove {n : ℕ | poissonRenewalArrival n ω ≤ t} := by
    refine ⟨N, ?_⟩
    intro n hn
    by_contra hnN
    have hNn : N ≤ n := by omega
    have hmono := poisson_renewal_arrivals_monotone ω hNn
    exact (not_le_of_gt (hN'.trans_le hmono)) hn
  have hfinite : {n : ℕ | poissonRenewalArrival n ω ≤ t}.Finite :=
    Set.finite_iff_bddAbove.mpr hbdd
  exact Set.encard_lt_top_iff.mpr hfinite

/-- Every sample path has a nondecreasing arrival-count function. -/
theorem unit_rate_poisson_process_count_monotone (s t : ℝ) (hst : s ≤ t)
    (ω : PoissonClockSpace) :
    unitRatePoissonProcessCount s ω ≤ unitRatePoissonProcessCount t ω := by
  change {n | poissonRenewalArrival n ω ≤ s}.encard ≤
    {n | poissonRenewalArrival n ω ≤ t}.encard
  apply Set.encard_mono
  intro n hn
  exact hn.trans hst

/-- Complete iid-interarrival construction data for the actual counting
process: a standard rate-one exponential renewal representation, measurable
finite-time counts, and almost-sure nonexplosion. -/
theorem unit_rate_poisson_process_exponential_interarrival_construction :
    ProbabilityTheory.iIndepFun (fun _ : ℕ => inferInstance)
      unitRatePoissonProcessInterarrival poissonClockProbability ∧
    (∀ n, poissonClockProbability.map (unitRatePoissonProcessInterarrival n) = unitExpProbability) ∧
    (∀ t, Measurable (unitRatePoissonProcessCount t)) ∧
    (∀ t, ∀ᵐ ω ∂poissonClockProbability,
      unitRatePoissonProcessCount t ω < ⊤) ∧
    (∀ s t, s ≤ t → ∀ ω,
      unitRatePoissonProcessCount s ω ≤ unitRatePoissonProcessCount t ω) ∧
    (∀ᵐ ω ∂poissonClockProbability,
      Tendsto (fun n => poissonRenewalArrival n ω) atTop atTop) := by
  exact ⟨poissonExponentialClocks_independent,
    (fun n => poisson_exponential_clock_map n),
    unit_rate_poisson_process_count_measurable,
    unit_rate_poisson_process_count_finite_ae,
    unit_rate_poisson_process_count_monotone,
    poisson_renewal_arrivals_tendsto_top_ae⟩

theorem unit_rate_poisson_at_most_one_event (t : ℝ) :
    {ω | unitRatePoissonProcessCount t ω ≤ (1 : ℕ∞)} =
      {ω | t < unitRatePoissonProcessArrival 1 ω} := by
  ext ω
  exact unit_rate_poisson_count_le_iff t ω 1

theorem poisson_renewal_second_arrival_eq (ω : PoissonClockSpace) :
    poissonRenewalArrival 1 ω =
      poissonExponentialClock 0 ω + poissonExponentialClock 1 ω := by
  simp [poissonRenewalArrival, Finset.sum_range_succ]

theorem poisson_renewal_second_arrival_gamma_law :
    poissonClockProbability.map (poissonRenewalArrival 1) = gammaProbability := by
  have hind := poissonExponentialClocks_independent.indepFun
    (by norm_num : (0 : ℕ) ≠ 1)
  have hpair0 := (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    (poissonExponentialClock_measurable 0).aemeasurable
    (poissonExponentialClock_measurable 1).aemeasurable).mp hind
  rw [poisson_exponential_clock_map, poisson_exponential_clock_map] at hpair0
  have hp : poissonClockProbability.map
      (fun ω : PoissonClockSpace =>
        (poissonExponentialClock 0 ω, poissonExponentialClock 1 ω)) =
      unitExpProbability.prod unitExpProbability := hpair0
  have hsum : poissonClockProbability.map
      (fun ω => poissonExponentialClock 0 ω + poissonExponentialClock 1 ω) =
      independentAffineSum unitExpProbability unitExpProbability 1 := by
    have hmap := Measure.map_map (μ := poissonClockProbability)
      (g := fun z : ℝ × ℝ => z.1 + z.2)
      (f := fun ω : PoissonClockSpace =>
        (poissonExponentialClock 0 ω, poissonExponentialClock 1 ω))
      (measurable_fst.add measurable_snd)
      ((poissonExponentialClock_measurable 0).prod_mk
        (poissonExponentialClock_measurable 1))
    calc
      _ = (poissonClockProbability.map (fun ω : PoissonClockSpace =>
          (poissonExponentialClock 0 ω, poissonExponentialClock 1 ω))).map
            (fun z : ℝ × ℝ => z.1 + z.2) := by
              simpa only [Function.comp_def] using hmap.symm
      _ = independentAffineSum unitExpProbability unitExpProbability 1 := by
            rw [hp]
            simp [independentAffineSum]
  have harrival : poissonRenewalArrival 1 =
      (fun ω => poissonExponentialClock 0 ω + poissonExponentialClock 1 ω) :=
    funext poisson_renewal_second_arrival_eq
  rw [harrival, hsum, independent_exponential_pair_gamma]

/-- The constructed Poisson process has the asserted law for its actual second
arrival epoch. This uses the first two coordinates of the full independent
clock sequence, not a separately postulated exponential pair. -/
theorem unit_rate_poisson_process_second_arrival_law :
    poissonClockProbability.map (unitRatePoissonProcessArrival 1) = gammaProbability := by
  exact poisson_renewal_second_arrival_gamma_law

theorem unit_rate_poisson_at_most_one_arrival_probability (t : ℝ) (ht : 0 ≤ t) :
    poissonClockProbability {ω | unitRatePoissonProcessCount t ω ≤ (1 : ℕ∞)} =
      ENNReal.ofReal ((1 + t) * Real.exp (-t)) := by
  rw [unit_rate_poisson_at_most_one_event]
  change poissonClockProbability
    ((unitRatePoissonProcessArrival 1) ⁻¹' Ioi t) = _
  rw [← Measure.map_apply (poisson_renewal_arrival_measurable 1) measurableSet_Ioi,
    unit_rate_poisson_process_second_arrival_law, gamma_probability_tail t ht]
  simp [gammaSurvival]

end
end Sigma
