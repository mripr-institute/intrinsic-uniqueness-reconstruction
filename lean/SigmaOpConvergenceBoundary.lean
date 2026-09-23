import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import SigmaOpLaguerreResolventCompact
import SigmaOpDiagonalNuclear
import SigmaOpResolvent

namespace Sigma
noncomputable section
open Filter
open scoped ComplexConjugate ENNReal Topology
set_option maxHeartbeats 1200000

/-- The real multiplier underlying the slowly increasing boundary spectrum. -/
def boundarySpectralFunction (t : ℝ) : ℝ := Real.sqrt (Real.log (t + 3))

/-- A slowly increasing spectral sequence: its resolvent coefficients still
tend to zero, while every positive heat and shifted-zeta series diverges. -/
def boundaryEigenvalue (n : ℕ) : ℝ := boundarySpectralFunction n

theorem boundary_eigenvalue_nonneg (n : ℕ) : 0 ≤ boundaryEigenvalue n :=
  Real.sqrt_nonneg _

theorem boundary_eigenvalue_tendsto_atTop :
    Tendsto boundaryEigenvalue atTop atTop := by
  rw [tendsto_atTop]
  intro b
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ)+3)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_right atTop 3 tendsto_natCast_atTop_atTop)
  filter_upwards [hlog.eventually_ge_atTop (max b 0 ^ 2)] with n hn
  change b ≤ Real.sqrt (Real.log ((n : ℝ)+3))
  by_cases hb : b ≤ 0
  · exact hb.trans (Real.sqrt_nonneg _)
  · have hbpos : 0 ≤ b := le_of_lt (lt_of_not_ge hb)
    have hs := Real.sqrt_le_sqrt hn
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (le_max_right b 0)] at hs
    exact (le_max_left b 0).trans hs

private theorem boundary_half_power_not_summable :
    ¬ Summable (fun n : ℕ => ((n : ℝ) + 3) ^ (-(1/2 : ℝ))) := by
  intro h
  have h' : Summable (fun n : ℕ => ((n : ℝ) ^ (-(1/2 : ℝ)))) := by
    exact (summable_nat_add_iff 3).mp (by simpa using h)
  have hcrit := (Real.summable_nat_rpow (p := -(1/2 : ℝ))).mp h'
  norm_num at hcrit

theorem boundary_heat_eigenvalues_not_summable (t : ℝ) (ht : 0 < t) :
    ¬ Summable (fun n : ℕ => Real.exp (-t * boundaryEigenvalue n)) := by
  intro hs
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 3)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_right atTop 3 tendsto_natCast_atTop_atTop)
  have hev := hlog.eventually_ge_atTop (4*t^2)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hbound (n : ℕ) (hn : 4*t^2 ≤ Real.log ((n : ℝ)+3)) :
      Real.exp (-t * boundaryEigenvalue n) ≥
        ((n : ℝ)+3) ^ (-(1/2 : ℝ)) := by
    have hpos : 0 < Real.log ((n : ℝ)+3) := by
      have : 0 < 4*t^2 := by positivity
      linarith
    have hsqrt : 2*t ≤ Real.sqrt (Real.log ((n : ℝ)+3)) := by
      have hs := Real.sqrt_le_sqrt hn
      have heq : 4*t^2 = (2*t)^2 := by ring
      rw [heq, Real.sqrt_sq_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ 2*t)] at hs
      exact hs
    have hsqrt2 := mul_le_mul_of_nonneg_right hsqrt
      (Real.sqrt_nonneg (Real.log ((n : ℝ)+3)))
    rw [← sq, Real.sq_sqrt (le_of_lt hpos)] at hsqrt2
    have hmul : t * Real.sqrt (Real.log ((n : ℝ)+3)) ≤
        (Real.log ((n : ℝ)+3))/2 := by nlinarith
    have hexp := Real.exp_le_exp.mpr (neg_le_neg hmul)
    have hpow : Real.exp (-Real.log ((n : ℝ)+3)/2) =
        ((n : ℝ)+3) ^ (-(1/2 : ℝ)) := by
      rw [Real.rpow_def_of_pos (by linarith : 0 < (n : ℝ)+3)]
      congr 1
      ring
    calc
      Real.exp (-t * boundaryEigenvalue n) ≥ Real.exp (-Real.log ((n : ℝ)+3)/2) := by
        change Real.exp (-Real.log ((n : ℝ)+3)/2) ≤ _
        have hb : boundaryEigenvalue n = Real.sqrt (Real.log ((n : ℝ)+3)) := by
          simp [boundaryEigenvalue, boundarySpectralFunction, add_comm]
        rw [hb, neg_mul]
        simpa only [neg_div] using hexp
      _ = ((n : ℝ)+3) ^ (-(1/2 : ℝ)) := hpow
  have htailN : Summable (fun n : ℕ =>
      Real.exp (-t * boundaryEigenvalue (n+N))) :=
    (summable_nat_add_iff (f := fun n : ℕ => Real.exp (-t * boundaryEigenvalue n)) N).mpr hs
  have hcompN : Summable (fun n : ℕ =>
      (((n+N : ℕ) : ℝ)+3) ^ (-(1/2 : ℝ))) := by
    refine Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (by positivity) _)
      (fun n => ?_) htailN
    have hn : 4*t^2 ≤ Real.log (((n+N : ℕ) : ℝ)+3) :=
      hN (n+N) (by omega)
    simpa [Nat.cast_add, boundaryEigenvalue] using hbound (n+N) hn
  have hcomp : Summable (fun n : ℕ => ((n : ℝ)+3) ^ (-(1/2 : ℝ))) := by
    exact (summable_nat_add_iff
      (f := fun n : ℕ => ((n : ℝ)+3) ^ (-(1/2 : ℝ))) N).mp
      (by simpa [Nat.cast_add] using hcompN)
  exact boundary_half_power_not_summable hcomp

theorem boundary_zeta_eigenvalues_not_summable (s : ℝ) (hs : 0 < s) :
    ¬ Summable (fun n : ℕ => (1 + boundaryEigenvalue n) ^ (-s)) := by
  intro hsum
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 3)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_right atTop 3 tendsto_natCast_atTop_atTop)
  have hev := hlog.eventually_ge_atTop (4*s^2)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hbound (n : ℕ) (hn : 4*s^2 ≤ Real.log ((n : ℝ)+3)) :
      (1 + boundaryEigenvalue n) ^ (-s) ≥
        ((n : ℝ)+3) ^ (-(1/2 : ℝ)) := by
    let x := Real.log ((n : ℝ)+3)
    have hxpos : 0 < x := by
      have : 0 < 4*s^2 := by positivity
      dsimp [x]
      linarith
    have hsqrt : 2*s ≤ Real.sqrt x := by
      have h := Real.sqrt_le_sqrt hn
      have heq : 4*s^2 = (2*s)^2 := by ring
      rw [heq, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2*s)] at h
      simpa [x] using h
    have hlogsmall : Real.log (1 + Real.sqrt x) ≤ Real.sqrt x := by
      have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + Real.sqrt x)
      linarith
    have hsqrt2 := mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg x)
    rw [← sq, Real.sq_sqrt (le_of_lt hxpos)] at hsqrt2
    have hprod : s * Real.sqrt x ≤ x/2 := by nlinarith
    have harg : s * Real.log (1 + Real.sqrt x) ≤ x/2 :=
      (mul_le_mul_of_nonneg_left hlogsmall (le_of_lt hs)).trans hprod
    have harg' : -x/2 ≤ -s * Real.log (1 + Real.sqrt x) := by nlinarith [harg]
    have hexp : Real.exp (-x/2) ≤ Real.exp (-s * Real.log (1 + Real.sqrt x)) :=
      Real.exp_le_exp.mpr harg'
    have hpow : Real.exp (-x/2) = ((n : ℝ)+3) ^ (-(1/2 : ℝ)) := by
      dsimp [x]
      rw [Real.rpow_def_of_pos (by positivity : 0 < (n : ℝ)+3)]
      congr 1
      ring
    have hbase : 1 + boundaryEigenvalue n = 1 + Real.sqrt x := by
      simp [boundaryEigenvalue, boundarySpectralFunction, x, add_comm]
    calc
      (1 + boundaryEigenvalue n) ^ (-s) =
          Real.exp (-s * Real.log (1 + Real.sqrt x)) := by
        have hposbase : 0 < 1 + boundaryEigenvalue n := by
          linarith [boundary_eigenvalue_nonneg n]
        rw [Real.rpow_def_of_pos hposbase, hbase]
        congr 1
        ring
      _ ≥ Real.exp (-x/2) := hexp.ge
      _ = ((n : ℝ)+3) ^ (-(1/2 : ℝ)) := hpow
  have htailN : Summable (fun n : ℕ => (1+boundaryEigenvalue (n+N)) ^ (-s)) :=
    (summable_nat_add_iff (f := fun n : ℕ => (1+boundaryEigenvalue n)^(-s)) N).mpr hsum
  have hcompN : Summable (fun n : ℕ => (((n+N : ℕ) : ℝ)+3) ^ (-(1/2 : ℝ))) := by
    refine Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (by positivity) _)
      (fun n => ?_) htailN
    have hn : 4*s^2 ≤ Real.log (((n+N : ℕ) : ℝ)+3) := hN (n+N) (by omega)
    simpa [Nat.cast_add, boundaryEigenvalue] using hbound (n+N) hn
  have hcomp : Summable (fun n : ℕ => ((n : ℝ)+3) ^ (-(1/2 : ℝ))) :=
    (summable_nat_add_iff
      (f := fun n : ℕ => ((n : ℝ)+3) ^ (-(1/2 : ℝ))) N).mp
      (by simpa [Nat.cast_add] using hcompN)
  exact boundary_half_power_not_summable hcomp

theorem boundary_eigenvalue_monotone : Monotone boundaryEigenvalue := by
  intro m n hmn
  unfold boundaryEigenvalue
  apply Real.sqrt_le_sqrt
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  apply Real.log_le_log (by linarith)
  exact add_le_add_right (Nat.cast_le.mpr hmn) 3

def boundaryResolventCoefficient (n : ℕ) : ℝ := (1 + boundaryEigenvalue n)⁻¹

theorem boundary_resolvent_coefficient_nonneg (n : ℕ) :
    0 ≤ boundaryResolventCoefficient n := by
  apply inv_nonneg.mpr
  have h := boundary_eigenvalue_nonneg n
  linarith

theorem boundary_resolvent_coefficient_bound (n : ℕ) :
    |boundaryResolventCoefficient n| ≤ 1 := by
  have hnonneg := boundary_eigenvalue_nonneg n
  have hp : 0 < 1 + boundaryEigenvalue n := by linarith
  change |(1 + boundaryEigenvalue n)⁻¹| ≤ 1
  rw [abs_of_pos (inv_pos.mpr hp)]
  apply inv_le_one_of_one_le₀
  linarith

theorem boundary_resolvent_coefficient_antitone : Antitone boundaryResolventCoefficient := by
  intro m n hmn
  unfold boundaryResolventCoefficient
  have hmon := boundary_eigenvalue_monotone hmn
  exact inv_anti₀ (by linarith [boundary_eigenvalue_nonneg m])
    (add_le_add_left hmon 1)

def boundaryResolvent : LaguerreWeightedHilbert →L[ℂ] LaguerreWeightedHilbert :=
  laguerreBoundedDiagonal boundaryResolventCoefficient 1 zero_le_one
    boundary_resolvent_coefficient_bound

theorem boundary_resolvent_coordinate (x : LaguerreWeightedHilbert) (n : ℕ) :
    laguerreHilbertBasis.repr (boundaryResolvent x) n =
      (boundaryResolventCoefficient n : ℂ) * laguerreHilbertBasis.repr x n :=
  laguerre_bounded_diagonal_coordinate boundaryResolventCoefficient 1 zero_le_one
    boundary_resolvent_coefficient_bound x n

def boundaryResolventTruncation (N : ℕ) :
    LaguerreWeightedHilbert →L[ℂ] LaguerreWeightedHilbert :=
  ∑ n ∈ Finset.range N, laguerreRankOne n (boundaryResolventCoefficient n)

theorem boundary_resolvent_truncation_compact (N : ℕ) :
    IsCompactOperator (boundaryResolventTruncation N) := by
  have h (s : Finset ℕ) : IsCompactOperator
      (∑ n ∈ s, laguerreRankOne n (boundaryResolventCoefficient n) :
        LaguerreWeightedHilbert →L[ℂ] LaguerreWeightedHilbert) := by
    induction s using Finset.induction_on with
    | empty => simpa using (isCompactOperator_zero (M₁ := LaguerreWeightedHilbert)
        (M₂ := LaguerreWeightedHilbert))
    | @insert n s hn ih =>
      simpa only [Finset.sum_insert hn, ContinuousLinearMap.coe_add] using
        (laguerre_rank_one_compact n (boundaryResolventCoefficient n)).add ih
  exact h _

theorem boundary_resolvent_truncation_coordinate (N k : ℕ) (x : LaguerreWeightedHilbert) :
    laguerreHilbertBasis.repr (boundaryResolventTruncation N x) k =
      if k < N then (boundaryResolventCoefficient k : ℂ) *
        laguerreHilbertBasis.repr x k else 0 := by
  simp only [boundaryResolventTruncation, ContinuousLinearMap.sum_apply, map_sum,
    lp.coeFn_sum, Finset.sum_apply, laguerre_rank_one_coordinate]
  simp

theorem boundary_resolvent_truncation_error (N : ℕ) :
    ‖boundaryResolvent-boundaryResolventTruncation N‖ ≤
      boundaryResolventCoefficient N := by
  let tail : ℕ → ℝ := fun n => if n < N then 0 else boundaryResolventCoefficient n
  have htail (n : ℕ) : |tail n| ≤ boundaryResolventCoefficient N := by
    by_cases h : n < N
    · simp [tail, h, boundary_resolvent_coefficient_nonneg]
    · change |if n < N then 0 else boundaryResolventCoefficient n| ≤ _
      rw [if_neg h, abs_of_nonneg (boundary_resolvent_coefficient_nonneg n)]
      exact boundary_resolvent_coefficient_antitone (Nat.le_of_not_gt h)
  have he : boundaryResolvent-boundaryResolventTruncation N =
      laguerreBoundedDiagonal tail (boundaryResolventCoefficient N)
        (boundary_resolvent_coefficient_nonneg N) htail := by
    apply ContinuousLinearMap.ext
    intro x
    apply laguerreHilbertBasis.repr.injective
    apply lp.ext
    funext n
    change laguerreHilbertBasis.repr
      (boundaryResolvent x-boundaryResolventTruncation N x) n = _
    rw [map_sub]
    simp only [lp.coeFn_sub, Pi.sub_apply, boundary_resolvent_coordinate,
      boundary_resolvent_truncation_coordinate,
      laguerre_bounded_diagonal_coordinate tail (boundaryResolventCoefficient N)
        (boundary_resolvent_coefficient_nonneg N) htail x n]
    by_cases hn : n < N <;> simp [tail, hn]
  rw [he]
  exact ContinuousLinearMap.opNorm_le_bound _ (boundary_resolvent_coefficient_nonneg N)
    (laguerre_bounded_diagonal_norm tail (boundaryResolventCoefficient N)
      (boundary_resolvent_coefficient_nonneg N) htail)

theorem boundary_resolvent_truncation_tendsto :
    Tendsto (fun N => boundaryResolventTruncation N) atTop (𝓝 boundaryResolvent) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hden : Tendsto (fun n : ℕ => 1 + boundaryEigenvalue n) atTop atTop :=
    tendsto_atTop_add_const_left atTop 1 boundary_eigenvalue_tendsto_atTop
  have hcoeff : Tendsto boundaryResolventCoefficient atTop (𝓝 0) := by
    simpa [boundaryResolventCoefficient] using tendsto_inv_atTop_zero.comp hden
  exact squeeze_zero (fun N => norm_nonneg _)
    (fun N => by
      rw [norm_sub_rev]
      exact boundary_resolvent_truncation_error N) hcoeff

theorem boundary_resolvent_compact : IsCompactOperator boundaryResolvent :=
  isCompactOperator_of_tendsto boundary_resolvent_truncation_tendsto
    (Eventually.of_forall boundary_resolvent_truncation_compact)

def boundaryOperator : LaguerreWeightedHilbert →ₗ.[ℂ] LaguerreWeightedHilbert :=
  laguerreSpectralOperator boundarySpectralFunction

theorem boundary_operator_selfadjoint : IsSelfAdjoint boundaryOperator :=
  laguerre_spectral_selfAdjoint boundarySpectralFunction

theorem boundary_operator_nonnegative (x : boundaryOperator.domain) :
    0 ≤ (@inner ℂ LaguerreWeightedHilbert _ x.val (boundaryOperator x)).re := by
  let c := laguerreHilbertBasis.repr x.val
  let d := laguerreHilbertBasis.repr (boundaryOperator x)
  have hd (n : ℕ) : d n = (boundaryEigenvalue n : ℂ) * c n := by
    simpa [boundaryEigenvalue, boundarySpectralFunction] using
      laguerre_spectral_coordinate boundarySpectralFunction x n
  have hs : Summable (fun n : ℕ => @inner ℂ ℂ _ (c n) (d n)) := lp.summable_inner c d
  have hinner : @inner ℂ LaguerreWeightedHilbert _ x.val (boundaryOperator x) =
      ∑' n : ℕ, @inner ℂ ℂ _ (c n) (d n) := by
    rw [← laguerreHilbertBasis.repr.inner_map_map, lp.inner_eq_tsum]
  have hterm (n : ℕ) : @inner ℂ ℂ _ (c n) (d n) =
      ((boundaryEigenvalue n * Complex.normSq (c n) : ℝ) : ℂ) := by
    rw [hd, RCLike.inner_apply]
    calc
      star (c n) * ((boundaryEigenvalue n : ℝ) * c n) =
          (boundaryEigenvalue n : ℝ) * (star (c n) * c n) := by ring
      _ = ((boundaryEigenvalue n * Complex.normSq (c n) : ℝ) : ℂ) := by
        change (boundaryEigenvalue n : ℝ) *
          (conj (c n) * c n) = _
        rw [← Complex.normSq_eq_conj_mul_self]
        push_cast
        ring
  have hterm_norm (n : ℕ) :
      ‖@inner ℂ ℂ _ (c n) (d n)‖ = boundaryEigenvalue n * Complex.normSq (c n) := by
    rw [hterm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (boundary_eigenvalue_nonneg n) (Complex.normSq_nonneg _))]
  have hs' : Summable (fun n : ℕ => boundaryEigenvalue n * Complex.normSq (c n)) := by
    have hmul := lp.summable_mul
      (by rw [Real.isConjExponent_iff]; norm_num :
        (2 : ℝ≥0∞).toReal.IsConjExponent (2 : ℝ≥0∞).toReal) c d
    apply Summable.of_nonneg_of_le
      (fun n => mul_nonneg (boundary_eigenvalue_nonneg n) (Complex.normSq_nonneg _))
      (fun n => by rw [← hterm_norm n]; exact norm_inner_le_norm (𝕜 := ℂ) _ _) hmul
  rw [hinner, Complex.re_tsum hs]
  have hreal : (∑' n : ℕ, (@inner ℂ ℂ _ (c n) (d n)).re) =
      ∑' n : ℕ, boundaryEigenvalue n * Complex.normSq (c n) := by
    apply tsum_congr
    intro n
    rw [hterm]
    simp
  rw [hreal]
  apply tsum_nonneg
  intro n
  exact mul_nonneg (boundary_eigenvalue_nonneg n) (Complex.normSq_nonneg _)

theorem boundary_resolvent_denominator_ne_zero (n : ℕ) :
    (1 + (boundaryEigenvalue n : ℂ)) ≠ 0 := by
  exact_mod_cast (show (1 + boundaryEigenvalue n : ℝ) ≠ 0 by
    have := boundary_eigenvalue_nonneg n
    positivity)

/-- The compact diagonal operator above is the actual inverse of `1+A`,
including the maximal weighted-square-summability domain. -/
theorem boundary_resolvent_mem_domain (x : LaguerreWeightedHilbert) :
    boundaryResolvent x ∈ boundaryOperator.domain := by
  change Memℓp (fun n : ℕ => (boundaryEigenvalue n : ℂ) *
    laguerreHilbertBasis.repr (boundaryResolvent x) n) 2
  have he : (fun n : ℕ => (boundaryEigenvalue n : ℂ) *
      laguerreHilbertBasis.repr (boundaryResolvent x) n) =
      fun n => laguerreHilbertBasis.repr (x - (1 : ℂ) • boundaryResolvent x) n := by
    funext n
    rw [map_sub, map_smul, boundary_resolvent_coordinate]
    simp only [lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [boundary_resolvent_coordinate]
    change (boundaryEigenvalue n : ℂ) *
        ((boundaryResolventCoefficient n : ℂ) * laguerreHilbertBasis.repr x n) =
      laguerreHilbertBasis.repr x n -
        (1 : ℂ) * ((boundaryResolventCoefficient n : ℂ) * laguerreHilbertBasis.repr x n)
    rw [boundaryResolventCoefficient]
    field_simp [boundary_resolvent_denominator_ne_zero n]
    ring
  rw [he]
  exact (laguerreHilbertBasis.repr (x - (1 : ℂ) • boundaryResolvent x)).property

theorem boundary_resolvent_generator_action (x : LaguerreWeightedHilbert) :
    boundaryOperator ⟨boundaryResolvent x, boundary_resolvent_mem_domain x⟩ =
      x - (1 : ℂ) • boundaryResolvent x := by
  apply laguerreHilbertBasis.repr.injective
  apply lp.ext
  funext n
  rw [map_sub, map_smul]
  simp only [lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [show laguerreHilbertBasis.repr
      (boundaryOperator ⟨boundaryResolvent x, boundary_resolvent_mem_domain x⟩) n =
        (boundaryEigenvalue n : ℂ) *
          laguerreHilbertBasis.repr (boundaryResolvent x) n by
      simpa [boundaryOperator, boundaryEigenvalue, boundarySpectralFunction] using
        laguerre_spectral_coordinate boundarySpectralFunction
          ⟨boundaryResolvent x, boundary_resolvent_mem_domain x⟩ n]
  rw [boundary_resolvent_coordinate]
  change (boundaryEigenvalue n : ℂ) *
      ((boundaryResolventCoefficient n : ℂ) * laguerreHilbertBasis.repr x n) =
    laguerreHilbertBasis.repr x n -
      (1 : ℂ) * ((boundaryResolventCoefficient n : ℂ) * laguerreHilbertBasis.repr x n)
  rw [boundaryResolventCoefficient]
  field_simp [boundary_resolvent_denominator_ne_zero n]
  ring

theorem boundary_resolvent_right_inverse (x : LaguerreWeightedHilbert) :
    boundaryOperator ⟨boundaryResolvent x, boundary_resolvent_mem_domain x⟩ +
      (1 : ℂ) • boundaryResolvent x = x := by
  rw [boundary_resolvent_generator_action]
  exact sub_add_cancel _ _

theorem boundary_resolvent_left_inverse (x : boundaryOperator.domain) :
    boundaryResolvent (boundaryOperator x + (1 : ℂ) • x.val) = x.val := by
  apply laguerreHilbertBasis.repr.injective
  apply lp.ext
  funext n
  rw [boundary_resolvent_coordinate, map_add, map_smul]
  change (boundaryResolventCoefficient n : ℂ) *
      (laguerreHilbertBasis.repr (boundaryOperator x) n +
        (1 : ℂ) * laguerreHilbertBasis.repr x.val n) = _
  rw [show laguerreHilbertBasis.repr (boundaryOperator x) n =
        (boundaryEigenvalue n : ℂ) * laguerreHilbertBasis.repr x.val n by
      simpa [boundaryOperator, boundaryEigenvalue, boundarySpectralFunction] using
        laguerre_spectral_coordinate boundarySpectralFunction x n]
  change (boundaryResolventCoefficient n : ℂ) *
      ((boundaryEigenvalue n : ℂ) * laguerreHilbertBasis.repr x.val n +
        (1 : ℂ) * laguerreHilbertBasis.repr x.val n) = _
  rw [boundaryResolventCoefficient]
  field_simp [boundary_resolvent_denominator_ne_zero n]
  ring

theorem boundary_operator_has_compact_resolvent :
    OpIsResolvent boundaryOperator 1 boundaryResolvent ∧
      IsCompactOperator boundaryResolvent :=
  ⟨⟨boundary_resolvent_mem_domain, boundary_resolvent_right_inverse,
    boundary_resolvent_left_inverse⟩, boundary_resolvent_compact⟩

private theorem boundary_diagonal_basis_action (b : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n, |b n| ≤ C) (n : ℕ) :
    laguerreBoundedDiagonal b C hC hb (laguerreHilbertBasis n) =
      (b n : ℂ) • laguerreHilbertBasis n := by
  apply laguerreHilbertBasis.repr.injective
  apply lp.ext
  funext k
  rw [laguerre_bounded_diagonal_coordinate, map_smul, laguerreHilbertBasis.repr_self]
  change (b k : ℂ) * markedIntegerEigenvector n k =
    (b n : ℂ) * markedIntegerEigenvector n k
  by_cases hkn : k = n
  · subst k
    rfl
  · simp [markedIntegerEigenvector, lp.single_apply_ne, hkn]

def boundaryHeatCoefficient (t : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-t * boundaryEigenvalue n)

theorem boundary_heat_coefficient_bound (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    |boundaryHeatCoefficient t n| ≤ 1 := by
  rw [boundaryHeatCoefficient, abs_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht)
    (boundary_eigenvalue_nonneg n)

/-- The genuine bounded heat multiplier of the constructed diagonal operator. -/
def boundaryHeatOperator (t : ℝ) (ht : 0 ≤ t) :
    LaguerreWeightedHilbert →L[ℂ] LaguerreWeightedHilbert :=
  laguerreBoundedDiagonal (boundaryHeatCoefficient t) 1 zero_le_one
    (boundary_heat_coefficient_bound t ht)

theorem boundary_heat_operator_basis_action (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    boundaryHeatOperator t ht (laguerreHilbertBasis n) =
      (boundaryHeatCoefficient t n : ℂ) • laguerreHilbertBasis n := by
  exact boundary_diagonal_basis_action _ _ _ _ n

theorem boundary_heat_operator_not_trace_class (t : ℝ) (ht : 0 < t) :
    ¬ IsNuclearOperator (boundaryHeatOperator t ht.le) := by
  intro hn
  have hs := (diagonal_operator_nuclear_iff laguerreHilbertBasis
    (boundaryHeatOperator t ht.le) (fun n => (boundaryHeatCoefficient t n : ℂ))
    (boundary_heat_operator_basis_action t ht.le)).mp hn
  have hs' : Summable (fun n => boundaryHeatCoefficient t n) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, boundaryHeatCoefficient,
      abs_of_nonneg (Real.exp_pos _).le] using hs
  exact boundary_heat_eigenvalues_not_summable t ht hs'

def boundaryZetaCoefficient (s : ℝ) (n : ℕ) : ℝ :=
  (1 + boundaryEigenvalue n) ^ (-s)

theorem boundary_zeta_coefficient_bound (s : ℝ) (hs : 0 < s) (n : ℕ) :
    |boundaryZetaCoefficient s n| ≤ 1 := by
  rw [boundaryZetaCoefficient,
    abs_of_nonneg (Real.rpow_nonneg (by linarith [boundary_eigenvalue_nonneg n]) _)]
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · linarith [boundary_eigenvalue_nonneg n]
  · linarith

/-- The actual bounded shifted-zeta multiplier `(1+A)^(-s)`. -/
def boundaryZetaOperator (s : ℝ) (hs : 0 < s) :
    LaguerreWeightedHilbert →L[ℂ] LaguerreWeightedHilbert :=
  laguerreBoundedDiagonal (boundaryZetaCoefficient s) 1 zero_le_one
    (boundary_zeta_coefficient_bound s hs)

theorem boundary_zeta_operator_basis_action (s : ℝ) (hs : 0 < s) (n : ℕ) :
    boundaryZetaOperator s hs (laguerreHilbertBasis n) =
      (boundaryZetaCoefficient s n : ℂ) • laguerreHilbertBasis n :=
  boundary_diagonal_basis_action _ _ _ _ n

theorem boundary_zeta_operator_not_trace_class (s : ℝ) (hs : 0 < s) :
    ¬ IsNuclearOperator (boundaryZetaOperator s hs) := by
  intro hn
  have hseries := (diagonal_operator_nuclear_iff laguerreHilbertBasis
    (boundaryZetaOperator s hs) (fun n => (boundaryZetaCoefficient s n : ℂ))
    (boundary_zeta_operator_basis_action s hs)).mp hn
  have hsum : Summable (fun n => boundaryZetaCoefficient s n) := by
    convert hseries using 1
    funext n
    rw [Complex.norm_real, Real.norm_eq_abs, boundaryZetaCoefficient,
      abs_of_nonneg (Real.rpow_nonneg (by linarith [boundary_eigenvalue_nonneg n]) _)]
  exact boundary_zeta_eigenvalues_not_summable s hs hsum

/-- Exact boundary witness: the compact resolvent is genuine, while both
positive-parameter operator traces fail to be finite. -/
theorem compact_resolvent_without_positive_traces :
    IsSelfAdjoint boundaryOperator ∧
    (∀ x : boundaryOperator.domain,
    0 ≤ (@inner ℂ LaguerreWeightedHilbert _ x.val (boundaryOperator x)).re) ∧
    OpIsResolvent boundaryOperator 1 boundaryResolvent ∧
    IsCompactOperator boundaryResolvent ∧
    (∀ (t : ℝ) (ht : 0 < t),
      ¬ IsNuclearOperator (boundaryHeatOperator t ht.le)) ∧
    (∀ (s : ℝ) (hs : 0 < s),
      ¬ IsNuclearOperator (boundaryZetaOperator s hs)) := by
  refine ⟨boundary_operator_selfadjoint, boundary_operator_nonnegative,
    boundary_operator_has_compact_resolvent.1, boundary_operator_has_compact_resolvent.2,
    ?_, ?_⟩
  · intro t ht
    exact boundary_heat_operator_not_trace_class t ht
  · intro s hs
    exact boundary_zeta_operator_not_trace_class s hs

end
end Sigma
