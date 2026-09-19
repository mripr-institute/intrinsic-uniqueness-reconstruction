import SigmaProbGamma
import SigmaSelfConcordanceGeometry
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace Sigma
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

def remoteDensityBump (c : ℝ) : ContDiffBump c := ⟨1/2, 1, by norm_num, by norm_num⟩

theorem remote_density_bump_center (c : ℝ) : remoteDensityBump c c = 1 := by
  apply (remoteDensityBump c).one_of_mem_closedBall
  norm_num [remoteDensityBump, Metric.mem_closedBall]

theorem remote_density_bump_left {c x : ℝ} (hx : x ≤ c-1) :
    remoteDensityBump c x = 0 := by
  apply (remoteDensityBump c).zero_of_le_dist
  rw [Real.dist_eq]
  dsimp [remoteDensityBump]
  have hh := le_abs_self (c-x)
  rw [abs_sub_comm] at hh
  linarith

theorem remote_density_bump_right {c x : ℝ} (hx : c+1 ≤ x) :
    remoteDensityBump c x = 0 := by
  apply (remoteDensityBump c).zero_of_le_dist
  rw [Real.dist_eq]
  dsimp [remoteDensityBump]
  linarith [le_abs_self (x-c)]

def weightedDensityBump (c x : ℝ) : ℝ := SigmaPresentations.density x * remoteDensityBump c x

theorem weighted_density_bump_smooth (c : ℝ) : ContDiff ℝ ∞ (weightedDensityBump c) :=
  (contDiff_id.mul contDiff_id.neg.exp).mul (remoteDensityBump c).contDiff

theorem weighted_density_bump_compact (c : ℝ) : HasCompactSupport (weightedDensityBump c) :=
  (remoteDensityBump c).hasCompactSupport.mul_left

theorem weighted_density_bump_integrable (c : ℝ) : Integrable (weightedDensityBump c) :=
  (weighted_density_bump_smooth c).continuous.integrable_of_hasCompactSupport
    (weighted_density_bump_compact c)

theorem weighted_density_bump_mass_positive {c : ℝ} (hc : 1 < c) :
    0 < ∫ x : ℝ in Ioi 0, weightedDensityBump c x := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    have hx0 : x ≤ 0 := le_of_not_gt hx
    simp [weightedDensityBump, remote_density_bump_left (show x ≤ c-1 by linarith)])]
  apply (weighted_density_bump_smooth c).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (weighted_density_bump_compact c)
  · intro x
    by_cases hx : 0 < x
    · exact mul_nonneg (SigmaPresentations.density_pos hx).le (remoteDensityBump c).nonneg
    · have hx0 : x ≤ 0 := le_of_not_gt hx
      simp [weightedDensityBump, remote_density_bump_left (show x ≤ c-1 by linarith)]
  · show weightedDensityBump c c ≠ 0
    rw [weightedDensityBump, remote_density_bump_center, mul_one]
    exact (SigmaPresentations.density_pos (by linarith)).ne'

/-- Normalized positive smooth densities can agree near every observation in a
bounded region, the mode and both endpoints, yet differ in between. -/
theorem smooth_density_germ_nonidentification (R : ℝ) (hR : 1 ≤ R) :
    ∃ q : ℝ → ℝ, ContDiff ℝ ∞ q ∧ (∀ x > 0, 0 < q x) ∧
      IntegrableOn q (Ioi 0) ∧ (∫ x : ℝ in Ioi 0, q x) = 1 ∧
      (∀ x ≤ R+1, q x = SigmaPresentations.density x) ∧
      (∀ x ≥ R+7, q x = SigmaPresentations.density x) ∧
      q (R+3) ≠ SigmaPresentations.density (R+3) ∧
      HasCompactSupport (fun x => q x-SigmaPresentations.density x) := by
  let A := R+3
  let B := R+6
  let mA := ∫ x : ℝ in Ioi 0, weightedDensityBump A x
  let mB := ∫ x : ℝ in Ioi 0, weightedDensityBump B x
  have ha : 0 < mA := weighted_density_bump_mass_positive (by dsimp [A]; linarith)
  have hb : 0 < mB := weighted_density_bump_mass_positive (by dsimp [B]; linarith)
  let ε := 1/(2*(mA+mB))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεsum : ε*(mA+mB)=1/2 := by dsimp [ε]; field_simp; ring
  let q : ℝ → ℝ := fun x => SigmaPresentations.density x +
    ε*(mB*weightedDensityBump A x-mA*weightedDensityBump B x)
  have hiA := (weighted_density_bump_integrable A).integrableOn (s := Ioi 0)
  have hiB := (weighted_density_bump_integrable B).integrableOn (s := Ioi 0)
  refine ⟨q, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (contDiff_id.mul contDiff_id.neg.exp).add
      (contDiff_const.mul ((contDiff_const.mul (weighted_density_bump_smooth A)).sub
        (contDiff_const.mul (weighted_density_bump_smooth B))))
  · intro x hx
    have he : q x = SigmaPresentations.density x *
        (1+ε*(mB*remoteDensityBump A x-mA*remoteDensityBump B x)) := by
      dsimp [q, weightedDensityBump]
      ring
    rw [he]
    apply mul_pos (SigmaPresentations.density_pos hx)
    have h1 := (remoteDensityBump A).nonneg (x := x)
    have h2 := (remoteDensityBump B).le_one (x := x)
    have h3 : 0 ≤ ε*mB*remoteDensityBump A x := by positivity
    have h4 : ε*mA*remoteDensityBump B x ≤ ε*mA := by
      exact mul_le_of_le_one_right (mul_pos hε ha).le h2
    nlinarith
  · exact intrinsic_density_integrable.add (((hiA.const_mul mB).sub (hiB.const_mul mA)).const_mul ε)
  · dsimp [q]
    change (∫ x : ℝ in Ioi 0, SigmaPresentations.density x +
      ε*(((fun y => mB*weightedDensityBump A y)-(fun y => mA*weightedDensityBump B y)) x)) = 1
    rw [integral_add intrinsic_density_integrable
      (((hiA.const_mul mB).sub (hiB.const_mul mA)).const_mul ε),
      integral_mul_left]
    simp only [Pi.sub_apply]
    rw [integral_sub (hiA.const_mul mB) (hiB.const_mul mA),
      integral_mul_left, integral_mul_left, intrinsic_density_integral_one]
    change 1+ε*(mB*mA-mA*mB)=1
    ring
  · intro x hx
    have hA := remote_density_bump_left (show x ≤ A-1 by dsimp [A]; linarith)
    have hB := remote_density_bump_left (show x ≤ B-1 by dsimp [B]; linarith)
    simp [q, weightedDensityBump, hA, hB]
  · intro x hx
    have hA := remote_density_bump_right (show A+1 ≤ x by dsimp [A]; linarith)
    have hB := remote_density_bump_right (show B+1 ≤ x by dsimp [B]; linarith)
    simp [q, weightedDensityBump, hA, hB]
  · change q A ≠ SigmaPresentations.density A
    have hB := remote_density_bump_left (show A ≤ B-1 by dsimp [A, B]; linarith)
    have hp : 0 < SigmaPresentations.density A := SigmaPresentations.density_pos (by dsimp [A]; linarith)
    simp only [q, weightedDensityBump, remote_density_bump_center, hB, mul_one,
      mul_zero, sub_zero, ne_eq]
    intro he
    have hp' := mul_pos hε (mul_pos hb hp)
    linarith
  · have he : (fun x => q x-SigmaPresentations.density x) =
        fun x => ε*(mB*weightedDensityBump A x-mA*weightedDensityBump B x) := by
      funext x
      dsimp [q]
      ring
    rw [he]
    have he' : (fun x => ε*(mB*weightedDensityBump A x-mA*weightedDensityBump B x)) =
        fun x => ε*(mB*weightedDensityBump A x+(-mA)*weightedDensityBump B x) := by
      funext x
      ring
    rw [he']
    exact ((weighted_density_bump_compact A).mul_left.add
      (weighted_density_bump_compact B).mul_left).mul_left

theorem smooth_density_same_jet_counterexample (a : ℝ) :
    ∃ q : ℝ → ℝ, ContDiff ℝ ∞ q ∧ (∀ x > 0, 0 < q x) ∧
      IntegrableOn q (Ioi 0) ∧ (∫ x : ℝ in Ioi 0, q x) = 1 ∧
      (q =ᶠ[𝓝 a] SigmaPresentations.density) ∧
      (∀ n : ℕ, iteratedDeriv n q a = iteratedDeriv n SigmaPresentations.density a) ∧
      (q =ᶠ[𝓝 1] SigmaPresentations.density) ∧
      (q =ᶠ[𝓝 0] SigmaPresentations.density) ∧
      (q =ᶠ[atTop] SigmaPresentations.density) ∧
      ∃ x > 0, q x ≠ SigmaPresentations.density x := by
  let R := max a 1
  obtain ⟨q, hq, hp, hi, hm, hl, hr, hd, _⟩ :=
    smooth_density_germ_nonidentification R (le_max_right _ _)
  have he (x : ℝ) (hx : x ≤ R) : q =ᶠ[𝓝 x] SigmaPresentations.density := by
    filter_upwards [Iio_mem_nhds (show x < R+1 by linarith)] with y hy
    exact hl y (le_of_lt hy)
  have ha := he a (le_max_left _ _)
  refine ⟨q, hq, hp, hi, hm, ha, fun n => ha.iteratedDeriv_eq n,
    he 1 (le_max_right _ _), he 0 (by dsimp [R]; have := le_max_right a 1; linarith), ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop (R+7)] with x hx
    exact hr x hx
  · exact ⟨R+3, by dsimp [R]; have := le_max_right a 1; linarith, hd⟩

theorem compact_smooth_perturbation_strictConvex (χ : ℝ → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hs : HasCompactSupport χ) :
    ∃ η > 0, ∀ ε : ℝ, |ε| < η →
      StrictConvexOn ℝ (Ioi 0) (fun t => I t+ε*χ t) := by
  have hc1 : ContDiff ℝ ∞ (deriv χ) := (contDiff_infty_iff_deriv.mp hχ).2
  have hc2 : Continuous (deriv (deriv χ)) := hc1.continuous_deriv (by simp)
  have hw : Continuous (fun t : ℝ => t^2*deriv (deriv χ) t) :=
    (continuous_id.pow 2).mul hc2
  have hws : HasCompactSupport (fun t : ℝ => t^2*deriv (deriv χ) t) := hs.deriv.deriv.mul_left
  obtain ⟨B, hB⟩ := (hws.abs.isCompact_range hw.abs).bddAbove
  let K := |B|+1
  have hK : 0 < K := by dsimp [K]; positivity
  have hk : ∀ t : ℝ, |t^2*deriv (deriv χ) t| ≤ K := by
    intro t
    have hh := hB (mem_range_self t)
    change |t^2*deriv (deriv χ) t| ≤ B at hh
    dsimp [K]
    linarith [le_abs_self B]
  refine ⟨1/(2*K), by positivity, ?_⟩
  intro ε hε
  have hfirst (t : ℝ) (ht : 0 < t) :
      HasDerivAt (fun t => I t+ε*χ t) (deriv I t+ε*deriv χ t) t :=
    ((SigmaBase.potential_hasDerivAt ht).differentiableAt.hasDerivAt).add
      (((contDiff_infty_iff_deriv.mp hχ).1 t).hasDerivAt.const_mul ε)
  apply strictConvexOn_of_deriv2_pos' (convex_Ioi (0 : ℝ))
    (fun t ht => (hfirst t ht).continuousAt.continuousWithinAt)
  intro t ht
  have hd : HasDerivAt (deriv (fun t => I t+ε*χ t))
      (1/t^2+ε*deriv (deriv χ) t) t := by
    have hh := (sc_intrinsic_second_hasDerivAt ht).add
      (((contDiff_infty_iff_deriv.mp hc1).1 t).hasDerivAt.const_mul ε)
    apply hh.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with x hx
    exact (hfirst x hx).deriv
  change 0 < deriv (deriv (fun t => I t+ε*χ t)) t
  rw [hd.deriv]
  have he : |ε*(t^2*deriv (deriv χ) t)| < 1/2 := by
    rw [abs_mul]
    have hh := (mul_le_mul_of_nonneg_left (hk t) (abs_nonneg ε)).trans_lt
      (mul_lt_mul_of_pos_right hε hK)
    have heq : (1/(2*K))*K=1/2 := by field_simp; ring
    simpa only [heq] using hh
  have hp : 0 < 1+ε*(t^2*deriv (deriv χ) t) := by
    have hh := neg_abs_le (ε*(t^2*deriv (deriv χ) t))
    linarith
  have ht2 : 0 < t^2 := sq_pos_of_pos ht
  have heq : t^2*(1/t^2+ε*deriv (deriv χ) t)=1+ε*(t^2*deriv (deriv χ) t) := by
    field_simp
    ring
  exact (mul_pos_iff_of_pos_left ht2).mp (heq.symm ▸ hp)

theorem smooth_potential_extension_counterexample :
    ∃ J : ℝ → ℝ, ContDiffOn ℝ ∞ J (Ioi 0) ∧ StrictConvexOn ℝ (Ioi 0) J ∧
      (J =ᶠ[𝓝 1] I) ∧ (∀ n : ℕ, iteratedDeriv n J 1=iteratedDeriv n I 1) ∧
      (∀ s ≥ 0, deriv J (1+s)=deriv I (1+s)) ∧ J (3/8) ≠ I (3/8) := by
  let χ : ContDiffBump (3/8 : ℝ) := ⟨1/16, 1/8, by norm_num, by norm_num⟩
  have hc : ContDiff ℝ ∞ (χ : ℝ → ℝ) := χ.contDiff
  obtain ⟨η, hη, hconv⟩ := compact_smooth_perturbation_strictConvex χ hc χ.hasCompactSupport
  let ε := η/2
  have hε : 0 < ε := half_pos hη
  have he : |ε| < η := by rw [abs_of_pos hε]; dsimp [ε]; linarith
  let J : ℝ → ℝ := fun t => I t+ε*χ t
  have hzero : ∀ t ≥ (1/2 : ℝ), χ t=0 := by
    intro t ht
    apply χ.zero_of_le_dist
    rw [Real.dist_eq]
    dsimp [χ]
    linarith [le_abs_self (t-3/8)]
  have heq (x : ℝ) (hx : (1/2 : ℝ)<x) : J =ᶠ[𝓝 x] I := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    simp [J, hzero t (le_of_lt ht)]
  have hg := heq 1 (by norm_num)
  refine ⟨J, ?_, hconv ε he, hg, fun n => hg.iteratedDeriv_eq n, ?_, ?_⟩
  · have hI : ContDiffOn ℝ ∞ I (Ioi 0) :=
      (contDiffOn_id.sub contDiffOn_const).sub
        (contDiffOn_id.log (fun t ht => (ne_of_gt ht)))
    exact hI.add (contDiffOn_const.mul hc.contDiffOn)
  · intro s hs
    exact (heq (1+s) (by linarith)).deriv_eq
  · have hχ : χ (3/8)=1 := by
      apply χ.one_of_mem_closedBall
      norm_num [χ, Metric.mem_closedBall]
    dsimp [J]
    rw [hχ, mul_one]
    linarith

end
end Sigma
