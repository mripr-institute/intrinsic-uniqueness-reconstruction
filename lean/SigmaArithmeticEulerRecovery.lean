import SigmaArithmeticEulerGenerators
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace Sigma
noncomputable section
open Set Filter
open scoped Topology BigOperators

def realEulerLogTerm (q : ℝ) (m : ℕ) (s : ℝ) (k : ℕ) : ℝ :=
  (m : ℝ) / (k + 1) * (q ^ (-s)) ^ (k + 1)

theorem real_euler_log_term_nonneg {q : ℝ} (hq : 0 < q) (m : ℕ) (s : ℝ) (k : ℕ) :
    0 ≤ realEulerLogTerm q m s k := by
  unfold realEulerLogTerm
  positivity

theorem real_euler_log_factor_hasSum {q s : ℝ} (hq : 1 < q) (hs : 0 < s) (m : ℕ) :
    HasSum (realEulerLogTerm q m s) (Real.log (realEulerFactor q m s)) := by
  have hp := Real.rpow_pos_of_pos (lt_trans zero_lt_one hq) (-s)
  have hlt := Real.rpow_lt_one_of_one_lt_of_neg hq (neg_neg_of_pos hs)
  have hh := (Real.hasSum_pow_div_log_of_abs_lt_one (by rwa [abs_of_pos hp])).mul_left (m : ℝ)
  rw [real_euler_log_factor]
  convert hh using 1
  funext k
  unfold realEulerLogTerm
  ring

theorem real_euler_log_double_hasSum {Q : Set ℝ} {m : Q → ℕ} {s Z : ℝ}
    (hQ : ∀ q ∈ Q, 1 < q) (hs : 0 < s) (hZ : 0 < Z)
    (hprod : HasProd (fun q : Q => realEulerFactor q (m q) s) Z) :
    HasSum (fun p : Q × ℕ => realEulerLogTerm p.1 (m p.1) s p.2) (Real.log Z) := by
  have hrows := fun q : Q => real_euler_log_factor_hasSum (hQ q q.property) hs (m q)
  have hlog := real_euler_product_log_hasSum hQ hs hZ hprod
  have hsum : Summable (fun p : Q × ℕ => realEulerLogTerm p.1 (m p.1) s p.2) := by
    apply (summable_prod_of_nonneg (fun p => real_euler_log_term_nonneg (by linarith [hQ p.1 p.1.property]) _ _ _)).mpr
    refine ⟨fun q => (hrows q).summable, ?_⟩
    simpa only [(hrows _).tsum_eq] using hlog.summable
  exact hsum.hasSum_iff.mpr ((hsum.hasSum.prod_fiberwise hrows).unique hlog)

theorem real_euler_scaled_term {q a : ℝ} (hq : 0 < q) (ha : 0 ≤ a)
    (m k : ℕ) (s : ℝ) :
    a ^ s * realEulerLogTerm q m s k =
      (m : ℝ) / (k + 1) * (a / q ^ (k + 1)) ^ s := by
  unfold realEulerLogTerm
  rw [Real.div_rpow ha (pow_nonneg hq.le _), Real.rpow_neg hq.le,
    inv_pow, ← Real.rpow_natCast_mul hq.le, mul_comm (↑(k+1) : ℝ) s,
    Real.rpow_mul_natCast hq.le]
  ring

theorem real_euler_ratio_bounds {Q : Set ℝ} (hQ : ∀ q ∈ Q, 1 < q)
    (a : Q) (hmin : ∀ q : Q, (a : ℝ) ≤ q) (q : Q) (k : ℕ) :
    0 < (a : ℝ) / (q : ℝ) ^ (k + 1) ∧ (a : ℝ) / (q : ℝ) ^ (k + 1) ≤ 1 := by
  have hq := hQ q q.property
  have ha := hQ a a.property
  have hp : (q : ℝ) ≤ (q : ℝ) ^ (k + 1) := by
    simpa only [pow_one] using pow_le_pow_right₀ hq.le (show 1 ≤ k + 1 by omega)
  exact ⟨div_pos (by linarith) (pow_pos (by linarith) _),
    (div_le_one (pow_pos (by linarith) _)).mpr ((hmin q).trans hp)⟩

/-- The multiplicity recovery limit is derived from positive product convergence,
not from an assumed asymptotic expansion or a locally finite enumeration. -/
theorem real_euler_least_multiplicity_limit {Q : Set ℝ} {m : Q → ℕ} {s₀ : ℝ}
    {Z : ℝ → ℝ} (hQ : ∀ q ∈ Q, 1 < q) (hs₀ : 0 < s₀)
    (hZ : ∀ s, s₀ ≤ s → 0 < Z s)
    (hprod : ∀ s, s₀ ≤ s → HasProd (fun q : Q => realEulerFactor q (m q) s) (Z s))
    (a : Q) (hmin : ∀ q : Q, (a : ℝ) ≤ q) :
    Tendsto (fun s : ℝ => (a : ℝ) ^ s * Real.log (Z s)) atTop (𝓝 (m a : ℝ)) := by
  classical
  let F : ℝ → Q × ℕ → ℝ := fun s p => (a : ℝ) ^ s * realEulerLogTerm p.1 (m p.1) s p.2
  let g : Q × ℕ → ℝ := fun p => if p = (a, 0) then (m a : ℝ) else 0
  have ha : 0 < (a : ℝ) := by linarith [hQ a a.property]
  have hsum : Summable (F s₀) :=
    (real_euler_log_double_hasSum hQ hs₀ (hZ _ le_rfl) (hprod _ le_rfl)).summable.mul_left _
  have hlim : ∀ p : Q × ℕ, Tendsto (fun s => F s p) atTop (𝓝 (g p)) := by
    rintro ⟨q, k⟩
    have hq : 0 < (q : ℝ) := by linarith [hQ q q.property]
    simp only [F, real_euler_scaled_term hq ha.le, g]
    by_cases hp : (q, k) = (a, 0)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj_iff.mp hp
      simp [ha.ne']
    · rw [if_neg hp]
      have hlt : (a : ℝ) < (q : ℝ) ^ (k + 1) := by
        by_cases hk : k = 0
        · subst k
          simp only [zero_add, pow_one]
          apply lt_of_le_of_ne (hmin q)
          intro he
          exact hp (Prod.ext (Subtype.ext he.symm) rfl)
        · exact (hmin q).trans_lt (lt_self_pow₀ (hQ q q.property) (by omega))
      have hr := real_euler_ratio_bounds hQ a hmin q k
      have ht := tendsto_rpow_atTop_of_base_lt_one ((a : ℝ) / (q : ℝ) ^ (k+1))
        (by linarith [hr.1]) ((div_lt_one (pow_pos hq _)).mpr hlt)
      simpa using ht.const_mul ((m q : ℝ) / (k + 1))
  have hb : ∀ᶠ s : ℝ in atTop, ∀ p, ‖F s p‖ ≤ F s₀ p := by
    filter_upwards [eventually_ge_atTop s₀] with s hs p
    rcases p with ⟨q,k⟩
    have hq : 0 < (q : ℝ) := by linarith [hQ q q.property]
    have hr := real_euler_ratio_bounds hQ a hmin q k
    simp only [F, real_euler_scaled_term hq ha.le]
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hr.1 hr.2 hs) (by positivity)
  have ht := tendsto_tsum_of_dominated_convergence hsum hlim hb
  have hg : (∑' p, g p) = (m a : ℝ) := by simp [g]
  rw [hg] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop s₀] with s hs
  exact ((real_euler_log_double_hasSum hQ (hs₀.trans_le hs) (hZ s hs)
    (hprod s hs)).mul_left ((a : ℝ)^s)).tsum_eq

/-- The first recovery limit follows from the positive multiplicity limit, with
the actual logarithm of the Euler product and its real negative reciprocal power. -/
theorem real_euler_least_generator_limit {Q : Set ℝ} {m : Q → ℕ} {s₀ : ℝ}
    {Z : ℝ → ℝ} (hQ : ∀ q ∈ Q, 1 < q) (hm : ∀ q, 0 < m q) (hs₀ : 0 < s₀)
    (hZ : ∀ s, s₀ ≤ s → 0 < Z s)
    (hprod : ∀ s, s₀ ≤ s → HasProd (fun q : Q => realEulerFactor q (m q) s) (Z s))
    (a : Q) (hmin : ∀ q : Q, (a : ℝ) ≤ q) :
    Tendsto (fun s : ℝ => (Real.log (Z s)) ^ (-(1 : ℝ) / s)) atTop (𝓝 (a : ℝ)) := by
  have ha : 0 < (a : ℝ) := by linarith [hQ a a.property]
  have hmpos : (0 : ℝ) < m a := by exact_mod_cast hm a
  have ht := real_euler_least_multiplicity_limit hQ hs₀ hZ hprod a hmin
  have hlog := ht.log hmpos.ne'
  have hquot := hlog.div_atTop tendsto_id
  have he₀ : Tendsto (fun s : ℝ => Real.log (a : ℝ) -
      Real.log ((a : ℝ) ^ s * Real.log (Z s)) / s) atTop (𝓝 (Real.log (a : ℝ))) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub hquot)
  have he := Real.continuous_exp.continuousAt.tendsto.comp he₀
  rw [Real.exp_log ha] at he
  apply he.congr'
  filter_upwards [eventually_ge_atTop s₀] with s hs
  have hspos := hs₀.trans_le hs
  have hlogpos : 0 < Real.log (Z s) := Real.log_pos
    (real_euler_product_gt_one hQ hm hspos (hZ s hs) (hprod s hs) ⟨a, a.property⟩)
  rw [Real.rpow_def_of_pos hlogpos]
  change Real.exp (Real.log (a : ℝ) - Real.log ((a : ℝ)^s * Real.log (Z s)) / s) =
    Real.exp (Real.log (Real.log (Z s)) * (-1 / s))
  apply congrArg Real.exp
  rw [Real.log_mul (Real.rpow_pos_of_pos ha s).ne' hlogpos.ne', Real.log_rpow ha]
  field_simp
  ring

/-- Both displayed B4 limits, with existence of a least generator derived from
the paper's terminal-ray positive convergence hypothesis. -/
theorem real_euler_multiset_recovery_limits {Q : Set ℝ} {m : Q → ℕ} {Z : ℝ → ℝ}
    (hQ : ∀ q ∈ Q, 1 < q) (hm : ∀ q, 0 < m q) (hne : Q.Nonempty)
    (hconv : ∃ S : ℝ, ∀ s, S ≤ s → 0 < Z s ∧
      HasProd (fun q : Q => realEulerFactor q (m q) s) (Z s)) :
    ∃ a : Q, (∀ q : Q, (a : ℝ) ≤ q) ∧
      Tendsto (fun s : ℝ => (Real.log (Z s)) ^ (-(1 : ℝ) / s)) atTop (𝓝 (a : ℝ)) ∧
      Tendsto (fun s : ℝ => (a : ℝ) ^ s * Real.log (Z s)) atTop (𝓝 (m a : ℝ)) := by
  obtain ⟨S, hS⟩ := hconv
  let s₀ := max S 1
  have hs₀ : 0 < s₀ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hconv' : ∀ s, s₀ ≤ s → 0 < Z s ∧
      HasProd (fun q : Q => realEulerFactor q (m q) s) (Z s) :=
    fun s hs => hS s ((le_max_left _ _).trans hs)
  obtain ⟨a, ha, _⟩ := real_euler_generators_least hQ hm hs₀
    (hconv' _ le_rfl).1 (hconv' _ le_rfl).2 hne
  let a' : Q := ⟨a, ha.1⟩
  have hmin : ∀ q : Q, (a' : ℝ) ≤ q := fun q => ha.2 q.property
  exact ⟨a', hmin,
    real_euler_least_generator_limit hQ hm hs₀ (fun s hs => (hconv' s hs).1)
      (fun s hs => (hconv' s hs).2) a' hmin,
    real_euler_least_multiplicity_limit hQ hs₀ (fun s hs => (hconv' s hs).1)
      (fun s hs => (hconv' s hs).2) a' hmin⟩

end
end Sigma
