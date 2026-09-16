import SigmaPresentations
import Mathlib.Topology.Algebra.Order.Archimedean

namespace Sigma
noncomputable section
open Set Filter
open scoped Topology

def gumbelCDF (x : ℝ) : ℝ := Real.exp (-Real.exp (-x))

theorem gumbel_cdf_positive (x : ℝ) : 0 < gumbelCDF x := Real.exp_pos _

theorem gumbel_cdf_lt_one (x : ℝ) : gumbelCDF x < 1 := by
  exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos (Real.exp_pos _))

theorem gumbel_cdf_monotone : Monotone gumbelCDF := by
  intro x y hxy
  apply Real.exp_le_exp.mpr
  exact neg_le_neg (Real.exp_le_exp.mpr (neg_le_neg hxy))

theorem gumbel_cdf_anchor : gumbelCDF 0 = Real.exp (-1) := by
  simp [gumbelCDF]

theorem gumbel_max_law (n : ℕ) (hn : 0 < n) (x : ℝ) :
    gumbelCDF (x + Real.log n) ^ n = gumbelCDF x := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [gumbelCDF, ← Real.exp_nat_mul, gumbelCDF]
  congr 1
  simp only [neg_add, Real.exp_add, Real.exp_neg, Real.exp_log hnR]
  field_simp
  ring

theorem gumbel_max_two (x : ℝ) :
    gumbelCDF (x + Real.log 2) ^ 2 = gumbelCDF x := by
  simpa using gumbel_max_law 2 (by norm_num) x

theorem gumbel_max_three (x : ℝ) :
    gumbelCDF (x + Real.log 3) ^ 3 = gumbelCDF x := by
  simpa using gumbel_max_law 3 (by norm_num) x

theorem no_positive_log_two_three_relation (m n : ℕ) (hn : 0 < n) :
    (n : ℝ) * Real.log 2 ≠ (m : ℝ) * Real.log 3 := by
  intro h
  have he := congrArg Real.exp h
  rw [Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<2),
    Real.exp_log (by norm_num : (0:ℝ)<3)] at he
  have hnat : 2 ^ n = 3 ^ m := by exact_mod_cast he
  have hdiv : 2 ∣ 3 ^ m := by
    rw [← hnat]
    exact dvd_pow_self 2 (Nat.ne_of_gt hn)
  have hodd : Odd (3 ^ m) := (show Odd (3 : ℕ) from ⟨1, by norm_num⟩).pow
  exact (Nat.not_even_iff_odd.mpr hodd) ((even_iff_two_dvd).mpr hdiv)

theorem log_two_three_dense (G : AddSubgroup ℝ)
    (h2 : Real.log 2 ∈ G) (h3 : Real.log 3 ∈ G) : Dense (G : Set ℝ) := by
  rcases G.dense_or_cyclic with hd | ⟨a, ha⟩
  · exact hd
  · rw [ha] at h2 h3
    obtain ⟨m, hm⟩ := AddSubgroup.mem_closure_singleton.mp h2
    obtain ⟨n, hn⟩ := AddSubgroup.mem_closure_singleton.mp h3
    simp only [zsmul_eq_mul] at hm hn
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hn0 : n ≠ 0 := by intro hh; simp [hh] at hn; linarith
    have he : (n : ℝ) * Real.log 2 = (m : ℝ) * Real.log 3 := by
      rw [← hm, ← hn]
      ring
    have hab := congrArg abs he
    rw [abs_mul, abs_mul, abs_of_pos hl2, abs_of_pos hl3] at hab
    have hnabs : 0 < n.natAbs := Int.natAbs_pos.mpr hn0
    have he' : (n.natAbs : ℝ) * Real.log 2 = (m.natAbs : ℝ) * Real.log 3 := by
      simpa only [Int.cast_natAbs, Int.cast_abs] using hab
    exact False.elim (no_positive_log_two_three_relation m.natAbs n.natAbs hnabs he')

def exponentialShiftGroup (g : ℝ → ℝ) : AddSubgroup ℝ where
  carrier := {a | ∀ x, g (x + a) = Real.exp (-a) * g x}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb x
    rw [← add_assoc, hb, ha, neg_add, Real.exp_add]
    ring
  neg_mem' := by
    intro a ha x
    have he : g x = Real.exp (-a) * g (x + -a) := by
      simpa using ha (x + -a)
    apply mul_left_cancel₀ (Real.exp_ne_zero (-a))
    rw [← he, ← mul_assoc, ← Real.exp_add]
    simp

theorem antitone_eq_exp_of_dense_agreement (g : ℝ → ℝ) (hg : Antitone g)
    (A : Set ℝ) (hA : Dense A) (heq : ∀ a ∈ A, g a = Real.exp (-a)) :
    ∀ x, g x = Real.exp (-x) := by
  intro x
  have hl : ∀ n : ℕ, ∃ a ∈ A,
      x - 1 / ((n : ℝ) + 1) < a ∧ a < x := by
    intro n
    exact hA.exists_between (sub_lt_self x (by positivity))
  have hr : ∀ n : ℕ, ∃ a ∈ A,
      x < a ∧ a < x + 1 / ((n : ℝ) + 1) := by
    intro n
    exact hA.exists_between (lt_add_of_pos_right x (by positivity))
  choose l hlA hll hlr using hl
  choose r hrA hrl hrr using hr
  have hbase := tendsto_one_div_add_atTop_nhds_zero_nat
  have hleft : Tendsto l atTop (𝓝 x) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa using tendsto_const_nhds.sub hbase) tendsto_const_nhds
      (fun n => (hll n).le) (fun n => (hlr n).le)
  have hright : Tendsto r atTop (𝓝 x) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using tendsto_const_nhds.add hbase)
      (fun n => (hrl n).le) (fun n => (hrr n).le)
  apply le_antisymm
  · apply ge_of_tendsto' (Real.continuous_exp.continuousAt.tendsto.comp hleft.neg)
    intro n
    change g x ≤ Real.exp (-(l n))
    rw [← heq (l n) (hlA n)]
    exact hg (hlr n).le
  · apply le_of_tendsto' (Real.continuous_exp.continuousAt.tendsto.comp hright.neg)
    intro n
    change Real.exp (-(r n)) ≤ g x
    rw [← heq (r n) (hrA n)]
    exact hg (hrl n).le

theorem antitone_two_scale_rigidity (g : ℝ → ℝ) (hg : Antitone g)
    (hzero : g 0 = 1)
    (h2 : ∀ x, g (x + Real.log 2) = g x / 2)
    (h3 : ∀ x, g (x + Real.log 3) = g x / 3) :
    ∀ x, g x = Real.exp (-x) := by
  have h2G : Real.log 2 ∈ exponentialShiftGroup g := by
    intro x
    rw [h2, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    ring
  have h3G : Real.log 3 ∈ exponentialShiftGroup g := by
    intro x
    rw [h3, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    ring
  apply antitone_eq_exp_of_dense_agreement g hg (exponentialShiftGroup g)
    (log_two_three_dense _ h2G h3G)
  intro a ha
  simpa [hzero] using ha 0

theorem max_two_iterate (F : ℝ → ℝ) (a : ℝ)
    (h2 : ∀ x, F (x + a) ^ 2 = F x) (x : ℝ) (n : ℕ) :
    F (x + (n : ℝ) * a) ^ (2 ^ n) = F x := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hx : x + ((n + 1 : ℕ) : ℝ) * a = (x + (n : ℝ) * a) + a := by
        push_cast
        ring
      rw [hx, pow_succ', pow_mul, h2, ih]

theorem max_two_anchor_bounds (F : ℝ → ℝ) (hmono : Monotone F)
    (h2 : ∀ x, F (x + Real.log 2) ^ 2 = F x)
    (hzero : F 0 = Real.exp (-1)) : ∀ x, 0 < F x ∧ F x < 1 := by
  have ha : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hf0 : 0 < F 0 := hzero ▸ Real.exp_pos _
  have hf1 : F 0 < 1 := by rw [hzero]; exact Real.exp_lt_one_iff.mpr (by norm_num)
  intro x
  have hpos : 0 < F x := by
    obtain ⟨n, hn⟩ := exists_nat_gt (-x / Real.log 2)
    have hxn : 0 ≤ x + (n : ℝ) * Real.log 2 := by
      have := (div_lt_iff₀ ha).mp hn
      linarith
    have hshift : 0 < F (x + (n : ℝ) * Real.log 2) :=
      lt_of_lt_of_le hf0 (hmono hxn)
    rw [← max_two_iterate F (Real.log 2) h2 x n]
    exact pow_pos hshift _
  refine ⟨hpos, ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (x / Real.log 2)
  have hxn : x - (n : ℝ) * Real.log 2 ≤ 0 := by
    have := (div_lt_iff₀ ha).mp hn
    linarith
  have hshift : F (x - (n : ℝ) * Real.log 2) < 1 :=
    lt_of_le_of_lt (hmono hxn) hf1
  have hi := max_two_iterate F (Real.log 2) h2 (x - (n : ℝ) * Real.log 2) n
  simp only [sub_add_cancel] at hi
  rw [← hi] at hshift
  by_contra h
  exact (not_lt_of_ge (one_le_pow₀ (le_of_not_gt h))) hshift

/-- The complete P3 inverse. Monotonicity and the three exact observations suffice;
even the other CDF axioms and every regularity assumption are redundant. -/
theorem gumbel_two_max_laws_unique (F : ℝ → ℝ) (hmono : Monotone F)
    (h2 : ∀ x, F (x + Real.log 2) ^ 2 = F x)
    (h3 : ∀ x, F (x + Real.log 3) ^ 3 = F x)
    (hzero : F 0 = Real.exp (-1)) : F = gumbelCDF := by
  let g : ℝ → ℝ := fun x => -Real.log (F x)
  have hb := max_two_anchor_bounds F hmono h2 hzero
  have hg : Antitone g := by
    intro x y hxy
    exact neg_le_neg (Real.log_le_log (hb x).1 (hmono hxy))
  have hg0 : g 0 = 1 := by simp [g, hzero]
  have hg2 : ∀ x, g (x + Real.log 2) = g x / 2 := by
    intro x
    have he := congrArg Real.log (h2 x)
    rw [Real.log_pow] at he
    norm_num at he
    dsimp [g]
    linarith
  have hg3 : ∀ x, g (x + Real.log 3) = g x / 3 := by
    intro x
    have he := congrArg Real.log (h3 x)
    rw [Real.log_pow] at he
    norm_num at he
    dsimp [g]
    linarith
  have he := antitone_two_scale_rigidity g hg hg0 hg2 hg3
  funext x
  have hx : Real.log (F x) = -Real.exp (-x) := by
    have hh := he x
    dsimp [g] at hh
    linarith
  rw [← Real.exp_log (hb x).1, hx]
  rfl

theorem gumbel_cdf_continuous : Continuous gumbelCDF := by
  exact continuous_id.neg.rexp.neg.rexp

theorem gumbel_cdf_tendsto_atTop : Tendsto gumbelCDF atTop (𝓝 1) := by
  have he : Tendsto (fun x : ℝ => Real.exp (-x)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  simpa [gumbelCDF] using Real.continuous_exp.continuousAt.tendsto.comp he.neg

theorem gumbel_cdf_tendsto_atBot : Tendsto gumbelCDF atBot (𝓝 0) := by
  have he : Tendsto (fun x : ℝ => Real.exp (-x)) atBot atTop :=
    Real.tendsto_exp_atTop.comp tendsto_neg_atBot_atTop
  exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp he)

def gumbelDensity (x : ℝ) : ℝ := Real.exp (-x - Real.exp (-x))

theorem gumbel_cdf_derivative (x : ℝ) : HasDerivAt gumbelCDF (gumbelDensity x) x := by
  have he := (((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).neg).exp
  convert he using 1
  change Real.exp (-x - Real.exp (-x)) =
    Real.exp (-Real.exp (-x)) * -(Real.exp (-x) * -1)
  rw [sub_eq_add_neg, Real.exp_add]
  ring

theorem gumbel_density_intrinsic (x : ℝ) :
    gumbelDensity x = SigmaPresentations.density (Real.exp (-x)) := by
  unfold gumbelDensity SigmaPresentations.density
  rw [sub_eq_add_neg, Real.exp_add]

theorem gumbel_density_reconstructs (t : ℝ) (ht : 0 < t) :
    gumbelDensity (-Real.log t) = SigmaPresentations.density t := by
  rw [gumbel_density_intrinsic, neg_neg, Real.exp_log ht]

end
end Sigma
