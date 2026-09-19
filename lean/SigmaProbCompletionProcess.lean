import SigmaProbCompletion
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Finset.Sort

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators

/-- The joint law of an arbitrary finite independent measurable family is the
actual product of its marginal laws. -/
theorem independent_finite_joint_law {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun (fun _ => inferInstance) X P) :
    P.map (fun ω i => X i ω) = Measure.pi (fun i => P.map (X i)) := by
  apply Eq.symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (measurable_pi_lambda _ hm) (MeasurableSet.pi Set.countable_univ (fun i _ => hs i))]
  have he : (fun ω i => X i ω) ⁻¹' Set.pi Set.univ s = ⋂ i, X i ⁻¹' s i := by
    ext ω
    simp
  rw [he, hi.meas_iInter (fun i => ⟨s i, hs i, rfl⟩)]
  apply Finset.prod_congr rfl
  intro i _
  rw [Measure.map_apply (hm i) (hs i)]

/-- The finite-dimensional distribution obtained from independent Gamma
increments of the given durations, by taking their actual partial sums. -/
def gammaCompletionFiniteLaw {n : ℕ} (d : Fin n → ℝ≥0) : Measure (Fin n → ℝ) :=
  (Measure.pi (fun i => gammaCompletion (d i))).map
    (fun z i => ∑ j ∈ Finset.univ.filter (fun j => j ≤ i), z j)

theorem measurable_finite_partial_sums (n : ℕ) :
    Measurable (fun z : Fin n → ℝ => fun i =>
      ∑ j ∈ Finset.univ.filter (fun j => j ≤ i), z j) := by
  apply measurable_pi_lambda
  intro i
  exact Finset.measurable_sum _ (fun j _ => measurable_pi_apply j)

instance gamma_completion_finite_law_probability {n : ℕ} (d : Fin n → ℝ≥0) :
    IsProbabilityMeasure (gammaCompletionFiniteLaw d) := by
  unfold gammaCompletionFiniteLaw
  exact isProbabilityMeasure_map (measurable_finite_partial_sums n).aemeasurable

theorem gamma_completion_finite_joint_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (d : Fin n → ℝ≥0) (Z : Fin n → Ω → ℝ)
    (hm : ∀ i, Measurable (Z i)) (hi : iIndepFun (fun _ => inferInstance) Z P)
    (hZ : ∀ i, P.map (Z i) = gammaCompletion (d i)) :
    P.map (fun ω i => ∑ j ∈ Finset.univ.filter (fun j => j ≤ i), Z j ω) =
      gammaCompletionFiniteLaw d := by
  have hj := independent_finite_joint_law P Z hm hi
  simp_rw [hZ] at hj
  rw [gammaCompletionFiniteLaw, ← hj,
    Measure.map_map (measurable_finite_partial_sums n) (measurable_pi_lambda _ hm)]
  rfl

theorem fin_initial_sum_eq_range {n : ℕ} (i : Fin n) (g : ℕ → ℝ) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin n => j ≤ i), g j) =
      ∑ j ∈ Finset.range (i.val+1), g j := by
  apply Finset.sum_bij (fun j _ => j.val)
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  · intro a _ b _ hab
    exact Fin.ext hab
  · intro k hk
    have hk' : k < i.val+1 := Finset.mem_range.mp hk
    refine ⟨⟨k, lt_of_le_of_lt (Nat.le_of_lt_succ hk') i.isLt⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Nat.le_of_lt_succ hk'
  · intro j _
    rfl

/-- The finite-dimensional laws are forced for every supplied process with
independent increments of the prescribed laws and starting value zero. -/
theorem gamma_completion_process_finite_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hm : ∀ r, Measurable (X r)) (hzero : ∀ᵐ ω ∂P, X 0 ω = 0)
    {n : ℕ} (t : ℕ → ℝ≥0) (ht0 : t 0 = 0)
    (hi : iIndepFun (fun _ : Fin n => inferInstance)
      (fun i : Fin n => fun ω => X (t (i.val+1)) ω-X (t i.val) ω) P)
    (hl : ∀ i : Fin n,
      P.map (fun ω => X (t (i.val+1)) ω-X (t i.val) ω) =
        gammaCompletion (t (i.val+1)-t i.val)) :
    P.map (fun ω => fun i : Fin n => X (t (i.val+1)) ω) =
      gammaCompletionFiniteLaw (fun i : Fin n => t (i.val+1)-t i.val) := by
  have hh := gamma_completion_finite_joint_law P
    (fun i : Fin n => t (i.val+1)-t i.val)
    (fun i : Fin n => fun ω => X (t (i.val+1)) ω-X (t i.val) ω)
    (fun i => (hm _).sub (hm _)) hi hl
  rw [← hh]
  apply Measure.map_congr
  filter_upwards [hzero] with ω hω
  funext i
  rw [fin_initial_sum_eq_range i (fun j => X (t (j+1)) ω-X (t j) ω),
    Finset.sum_range_sub (fun j => X (t j) ω), ht0, hω, sub_zero]

/-- Independent increments are expressed by the native independence predicate
for every finite increasing sequence of observation times. -/
def HasIndependentNonnegativeTimeIncrements {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ (n : ℕ) (t : ℕ → ℝ≥0), Monotone t → t 0 = 0 →
    iIndepFun (fun _ : Fin n => inferInstance)
      (fun i : Fin n => fun ω => X (t (i.val+1)) ω-X (t i.val) ω) P

theorem process_independent_present_future {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hm : ∀ r, Measurable (X r)) (hzero : ∀ᵐ ω ∂P, X 0 ω = 0)
    (hi : HasIndependentNonnegativeTimeIncrements P X) (r s : ℝ≥0) :
    IndepFun (X r) (fun ω => X (r+s) ω-X r ω) P := by
  let t : ℕ → ℝ≥0 := fun k => if k = 0 then 0 else if k = 1 then r else r+s
  have ht : Monotone t := by
    intro a b hab
    dsimp [t]
    split_ifs with ha hb hb' ha' hb' <;> try omega
    all_goals first | exact zero_le _ | exact le_add_of_nonneg_right (zero_le _) | exact le_rfl
  have hz : t 0 = 0 := by simp [t]
  have hii := (hi 2 t ht hz).indepFun (show (0:Fin 2) ≠ 1 by decide)
  have hm0 : Measurable (fun ω => X r ω-X 0 ω) := (hm _).sub (hm _)
  have hm1 : Measurable (fun ω => X (r+s) ω-X r ω) := (hm _).sub (hm _)
  have hii' : IndepFun (fun ω => X r ω-X 0 ω) (fun ω => X (r+s) ω-X r ω) P := by
    simpa [t] using hii
  have he0 : P.map (fun ω => X r ω-X 0 ω) = P.map (X r) := by
    apply Measure.map_congr
    filter_upwards [hzero] with ω hω
    simp [hω]
  have he2 : P.map (fun ω => (X r ω-X 0 ω, X (r+s) ω-X r ω)) =
      P.map (fun ω => (X r ω, X (r+s) ω-X r ω)) := by
    apply Measure.map_congr
    filter_upwards [hzero] with ω hω
    simp [hω]
  apply (indepFun_iff_map_prod_eq_prod_map_map (hm r).aemeasurable hm1.aemeasurable).mpr
  have hh := (indepFun_iff_map_prod_eq_prod_map_map hm0.aemeasurable hm1.aemeasurable).mp hii'
  rwa [he0, he2] at hh

theorem stationary_independent_process_gamma_marginals {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hm : ∀ r, Measurable (X r)) (hzero : ∀ᵐ ω ∂P, X 0 ω = 0)
    (hpos : ∀ r, ∀ᵐ ω ∂P, 0 ≤ X r ω)
    (hi : HasIndependentNonnegativeTimeIncrements P X)
    (hstat : ∀ r s, P.map (fun ω => X (r+s) ω-X r ω) = P.map (X s))
    (hone : P.map (X 1) = gammaProbability) :
    (fun r => P.map (X r)) = gammaCompletion := by
  apply gamma_completion_unique
  · intro r
    exact isProbabilityMeasure_map (hm r).aemeasurable
  · intro r
    exact (ae_map_iff (hm r).aemeasurable measurableSet_Ici).mpr (hpos r)
  · intro r s
    have hpair := (indepFun_iff_map_prod_eq_prod_map_map (hm r).aemeasurable
      ((hm (r+s)).sub (hm r)).aemeasurable).mp
        (process_independent_present_future P X hm hzero hi r s)
    rw [hstat r s] at hpair
    rw [independentAffineSum, ← hpair,
      Measure.map_map (by fun_prop) ((hm r).prod_mk ((hm (r+s)).sub (hm r)))]
    congr 1
    funext ω
    simp
  · exact hone

/-- The starting value, stationary independent increment category, nonnegative
marginals and time-one Gamma law force every ordered finite-dimensional law. -/
theorem gamma_completion_process_fdd_unique {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hm : ∀ r, Measurable (X r)) (hzero : ∀ᵐ ω ∂P, X 0 ω = 0)
    (hpos : ∀ r, ∀ᵐ ω ∂P, 0 ≤ X r ω)
    (hi : HasIndependentNonnegativeTimeIncrements P X)
    (hstat : ∀ r s, P.map (fun ω => X (r+s) ω-X r ω) = P.map (X s))
    (hone : P.map (X 1) = gammaProbability)
    (n : ℕ) (t : ℕ → ℝ≥0) (ht : Monotone t) (ht0 : t 0 = 0) :
    P.map (fun ω => fun i : Fin n => X (t (i.val+1)) ω) =
      gammaCompletionFiniteLaw (fun i : Fin n => t (i.val+1)-t i.val) := by
  apply gamma_completion_process_finite_law P X hm hzero t ht0 (hi n t ht ht0)
  intro i
  have hh := hstat (t i.val) (t (i.val+1)-t i.val)
  rw [add_tsub_cancel_of_le (ht (Nat.le_succ _))] at hh
  rw [hh]
  exact congrFun (stationary_independent_process_gamma_marginals P X hm hzero hpos hi hstat hone) _

theorem finite_nonnegative_times_ordered_cover {n : ℕ} (u : Fin n → ℝ≥0) :
    ∃ (m : ℕ) (t : ℕ → ℝ≥0) (k : Fin n → Fin m),
      Monotone t ∧ t 0 = 0 ∧ ∀ i, t ((k i).val+1) = u i := by
  classical
  let S : Finset ℝ≥0 := insert 0 (Finset.univ.image u)
  have hS : 0 < S.card := Finset.card_pos.mpr ⟨0, Finset.mem_insert_self _ _⟩
  let e : Fin S.card ↪o ℝ≥0 := S.orderEmbOfFin rfl
  let j (a : ℕ) : Fin S.card := ⟨min a (S.card-1),
    lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hS (by norm_num))⟩
  let t : ℕ → ℝ≥0 := fun a => if a = 0 then 0 else e (j (a-1))
  have hj : Monotone j := by
    intro a b hab
    exact min_le_min_right _ hab
  have ht : Monotone t := by
    intro a b hab
    dsimp [t]
    split_ifs with ha hb
    · rfl
    · exact zero_le _
    · subst b
      have : a = 0 := Nat.eq_zero_of_le_zero hab
      contradiction
    · exact e.monotone (hj (Nat.sub_le_sub_right hab 1))
  have hu (i : Fin n) : u i ∈ S := Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  let k (i : Fin n) : Fin S.card := (S.orderIsoOfFin rfl).symm ⟨u i, hu i⟩
  refine ⟨S.card, t, k, ht, by simp [t], ?_⟩
  intro i
  have hk : j (k i).val = k i := by
    apply Fin.ext
    exact min_eq_left (Nat.le_pred_of_lt (k i).isLt)
  simp only [t, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
    Nat.add_sub_cancel]
  rw [hk]
  exact congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply ⟨u i, hu i⟩)

/-- Agreement on all increasing finite time lists entails agreement of arbitrary
finite-dimensional distributions, including repeated and unordered times. -/
theorem process_fdd_eq_of_ordered {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (Q : Measure Ω') (X : ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Ω' → ℝ)
    (hX : ∀ r, Measurable (X r)) (hY : ∀ r, Measurable (Y r))
    (he : ∀ (n : ℕ) (t : ℕ → ℝ≥0), Monotone t → t 0 = 0 →
      P.map (fun ω => fun i : Fin n => X (t (i.val+1)) ω) =
        Q.map (fun ω => fun i : Fin n => Y (t (i.val+1)) ω))
    (n : ℕ) (u : Fin n → ℝ≥0) :
    P.map (fun ω i => X (u i) ω) = Q.map (fun ω i => Y (u i) ω) := by
  obtain ⟨m,t,k,ht,ht0,hk⟩ := finite_nonnegative_times_ordered_cover u
  have hh := congrArg (fun ρ : Measure (Fin m → ℝ) =>
    ρ.map (fun z => fun i => z (k i))) (he m t ht ht0)
  dsimp only at hh
  rw [Measure.map_map (measurable_pi_lambda _ (fun i => measurable_pi_apply (k i)))
    (measurable_pi_lambda _ (fun i : Fin m => hX (t (i.val+1)))),
    Measure.map_map (measurable_pi_lambda _ (fun i => measurable_pi_apply (k i)))
    (measurable_pi_lambda _ (fun i : Fin m => hY (t (i.val+1))))] at hh
  simpa only [Function.comp_def, hk] using hh

/-- The supplied process category in P8. These are only the category's ordinary
requirements and the prescribed time-one marginal, not its conclusion. -/
def IsGammaTimeOneProcess {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ r, Measurable (X r)) ∧ (∀ᵐ ω ∂P, X 0 ω = 0) ∧
  (∀ r, ∀ᵐ ω ∂P, 0 ≤ X r ω) ∧
  HasIndependentNonnegativeTimeIncrements P X ∧
  (∀ r s, P.map (fun ω => X (r+s) ω-X r ω) = P.map (X s)) ∧
  P.map (X 1) = gammaProbability

/-- Any two supplied processes in the paper's category agree in every
finite-dimensional law, on arbitrary (also repeated or unordered) times. -/
theorem gamma_time_one_process_fdd_unique {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (Q : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Ω' → ℝ)
    (hX : IsGammaTimeOneProcess P X) (hY : IsGammaTimeOneProcess Q Y)
    (n : ℕ) (u : Fin n → ℝ≥0) :
    P.map (fun ω i => X (u i) ω) = Q.map (fun ω i => Y (u i) ω) := by
  apply process_fdd_eq_of_ordered P Q X Y hX.1 hY.1 _ n u
  intro m t ht ht0
  rw [gamma_completion_process_fdd_unique P X hX.1 hX.2.1 hX.2.2.1
    hX.2.2.2.1 hX.2.2.2.2.1 hX.2.2.2.2.2 m t ht ht0,
    gamma_completion_process_fdd_unique Q Y hY.1 hY.2.1 hY.2.2.1
    hY.2.2.2.1 hY.2.2.2.2.1 hY.2.2.2.2.2 m t ht ht0]

end
end Sigma
