import SigmaProbBoundaries
import SigmaProbSupport
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.MeasureTheory.Decomposition.SignedLebesgue
import Mathlib.MeasureTheory.Measure.OpenPos

namespace Sigma
noncomputable section

open MeasureTheory Set Filter
open scoped FourierTransform ContDiff Topology NNReal ENNReal

/-- A smooth compactly supported scalar function, viewed as a complex Schwartz function. -/
def compactSmoothSchwartz (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) : SchwartzMap ℝ ℂ where
  toFun x := (f x : ℂ)
  smooth' := by
    simpa only [Function.comp_apply] using Complex.ofRealCLM.contDiff.comp hf
  decay' := by
    intro k n
    let g : ℝ → ℝ := fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y : ℝ => (f y : ℂ)) x‖
    have hsmooth : ContDiff ℝ ∞ (fun y : ℝ => (f y : ℂ)) := by
      simpa only [Function.comp_apply] using Complex.ofRealCLM.contDiff.comp hf
    have hcompact : HasCompactSupport (fun y : ℝ => (f y : ℂ)) := by
      simpa only [Function.comp_apply] using hfc.comp_left Complex.ofReal_zero
    have hgcont : Continuous g := by
      exact (continuous_norm.pow k).mul
        (hsmooth.continuous_iteratedFDeriv (mod_cast le_top)).norm
    have hgc : HasCompactSupport g := by
      apply HasCompactSupport.mul_left
      exact (hcompact.iteratedFDeriv n).comp_left norm_zero
    obtain ⟨C, hC⟩ := hgcont.bounded_above_of_compact_support hgc
    refine ⟨C, fun x => ?_⟩
    simpa only [g, Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _)
      (norm_nonneg _))] using hC x

/-- A nonzero real even smooth bump whose support stays away from the origin. -/
theorem exists_even_smooth_fourier_bump :
    ∃ f : ℝ → ℝ,
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      (∀ x, f (-x) = f x) ∧
      (∀ x ∈ Ioo (-1 : ℝ) 1, f x = 0) ∧
      (∀ x, 0 ≤ f x) ∧ f (3 / 2) = 1 := by
  have hmem : Ioo (1 : ℝ) 2 ∈ 𝓝 (3 / 2 : ℝ) :=
    IsOpen.mem_nhds isOpen_Ioo (by norm_num)
  obtain ⟨b, hbsupp, hbcompact, hbsmooth, hbrange, hbval⟩ :=
    exists_smooth_tsupport_subset hmem
  let f : ℝ → ℝ := fun x => b x + b (-x)
  have hbnonneg : ∀ x, 0 ≤ b x := by
    intro x
    exact (hbrange ⟨x, rfl⟩).1
  refine ⟨f, hbsmooth.add (hbsmooth.comp contDiff_neg),
    hbcompact.add (hbcompact.comp_homeomorph (Homeomorph.neg ℝ)), ?_, ?_, ?_, ?_⟩
  · intro x
    dsimp [f]
    rw [neg_neg, add_comm]
  · intro x hx
    dsimp [f]
    have hbx : b x = 0 := by
      by_contra hn
      have hm : x ∈ tsupport b := subset_tsupport b hn
      have := hbsupp hm
      linarith [this.1, this.2, hx.1, hx.2]
    have hbnx : b (-x) = 0 := by
      by_contra hn
      have hm : -x ∈ tsupport b := subset_tsupport b hn
      have := hbsupp hm
      linarith [this.1, this.2, hx.1, hx.2]
    rw [hbx, hbnx, add_zero]
  · intro x
    exact add_nonneg (hbnonneg x) (hbnonneg (-x))
  · dsimp [f]
    rw [hbval]
    have hbneg : b (-(3 / 2 : ℝ)) = 0 := by
      by_contra hn
      have hm : -(3 / 2 : ℝ) ∈ tsupport b := subset_tsupport b hn
      have := hbsupp hm
      norm_num at this
    rw [hbneg, add_zero]

/-- A real integrable function with all absolute polynomial moments finite,
obtained as the real part of the inverse Fourier transform of a bump away
from the origin. -/
theorem exists_real_rapid_moment_null :
    ∃ h : ℝ → ℝ, Continuous h ∧ h ≠ 0 ∧
      (∀ n : ℕ, Integrable (fun x : ℝ => x ^ n * h x)) ∧
      ∀ n : ℕ, (∫ x : ℝ, x ^ n * h x) = 0 := by
  obtain ⟨f, hfsmooth, hfcompact, hfeven, hfzero, hfnonneg, hfval⟩ :=
    exists_even_smooth_fourier_bump
  let Φ : SchwartzMap ℝ ℂ := compactSmoothSchwartz f hfsmooth hfcompact
  let H : SchwartzMap ℝ ℂ := (SchwartzMap.fourierTransformCLE ℂ).symm Φ
  let h : ℝ → ℝ := fun x => (H x).re
  have hfint : Integrable f := hfsmooth.continuous.integrable_of_hasCompactSupport hfcompact
  have hfpos : 0 < ∫ x : ℝ, f x :=
    hfsmooth.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      hfcompact hfnonneg (by rw [hfval]; norm_num)
  have hH0 : H 0 = ((∫ x : ℝ, f x : ℝ) : ℂ) := by
    change ((SchwartzMap.fourierTransformCLE ℂ).symm Φ : ℝ → ℂ) 0 = _
    rw [SchwartzMap.fourierTransformCLE_symm_apply, Real.fourierIntegralInv_eq]
    simp only [inner_zero_right]
    rw [Real.fourierChar.map_zero_eq_one]
    simpa only [one_smul, Φ, compactSmoothSchwartz]
      using (integral_ofReal (μ := volume) (f := f) (𝕜 := ℂ))
  have hhne : h ≠ 0 := by
    intro he
    have hz := congrFun he 0
    dsimp [h] at hz
    rw [hH0] at hz
    norm_num at hz
    linarith
  have hhcont : Continuous h := Complex.continuous_re.comp H.continuous
  refine ⟨h, hhcont, hhne, ?_, ?_⟩
  · intro n
    have hnorm := H.integrable_pow_mul volume n
    apply hnorm.mono'
    · exact ((continuous_id.pow n).mul
        (Complex.continuous_re.comp H.continuous)).aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs]
      calc
        |x ^ n * h x| ≤ ‖x‖ ^ n * ‖H x‖ := by
          dsimp [h]
          rw [abs_mul, abs_pow]
          exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_abs _)
            (pow_nonneg (abs_nonneg _) _)
        _ = _ := rfl
  · intro n
    have hFourier : Real.fourierIntegral (fun x : ℝ => H x) = fun x => Φ x := by
      change (fun x => ((SchwartzMap.fourierTransformCLE ℂ) H) x) = fun x => Φ x
      rw [show (SchwartzMap.fourierTransformCLE ℂ) H = Φ by simp [H]]
    have hΦzero : (fun x : ℝ => Φ x) =ᶠ[𝓝 0] (0 : ℝ → ℂ) := by
      filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
        (by norm_num : (0 : ℝ) < 1)] with x hx
      change (f x : ℂ) = 0
      rw [hfzero x hx]
      norm_num
    have hderzero : iteratedDeriv n (Real.fourierIntegral (fun x : ℝ => H x)) 0 = 0 := by
      rw [hFourier]
      rw [hΦzero.iteratedDeriv_eq n]
      have hz : iteratedDeriv n (fun _ : ℝ => (0 : ℂ)) = 0 := by
        induction n with
        | zero => rfl
        | succ n ih =>
            rw [iteratedDeriv_succ, ih]
            funext x
            exact deriv_const x 0
      change iteratedDeriv n (fun _ : ℝ => (0 : ℂ)) 0 = 0
      rw [hz]
      rfl
    have hpowint : ∀ m : ℕ, Integrable (fun x : ℝ => x ^ m • H x) := by
      intro m
      apply (H.integrable_pow_mul volume m).mono'
      · exact ((continuous_id.pow m).smul H.continuous).aestronglyMeasurable
      · filter_upwards with x
        simp only [norm_smul, Real.norm_eq_abs, abs_pow]
        exact le_rfl
    have hd := congrFun (Real.iteratedDeriv_fourierIntegral
      (f := fun x : ℝ => H x) (N := ⊤) (n := n)
      (fun m _ => hpowint m) (mod_cast le_top)) 0
    rw [hderzero] at hd
    rw [Real.fourierIntegral_eq] at hd
    simp only [inner_zero_right, neg_zero, Real.fourierChar.map_zero_eq_one, one_smul] at hd
    have hconst : (-2 * (Real.pi : ℂ) * Complex.I) ^ n ≠ 0 := by
      apply pow_ne_zero
      exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        Complex.I_ne_zero
    have hfactor :
        (∫ x : ℝ, (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) ^ n * H x) =
          (-2 * (Real.pi : ℂ) * Complex.I) ^ n *
            ∫ x : ℝ, (x : ℂ) ^ n * H x := by
      calc
        (∫ x : ℝ, (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) ^ n * H x) =
            ∫ x : ℝ, (-2 * (Real.pi : ℂ) * Complex.I) ^ n •
              ((x : ℂ) ^ n * H x) := by
                apply integral_congr_ae
                filter_upwards with x
                rw [mul_pow]
                simp only [smul_eq_mul, mul_assoc]
        _ = (-2 * (Real.pi : ℂ) * Complex.I) ^ n •
              ∫ x : ℝ, (x : ℂ) ^ n * H x := integral_smul _ _
        _ = _ := rfl
    simp only [smul_eq_mul] at hd
    rw [hfactor] at hd
    have hcmoment : (∫ x : ℝ, (x : ℂ) ^ n * H x) = 0 := by
      exact (mul_eq_zero.mp hd.symm).resolve_left hconst
    have hint : Integrable (fun x : ℝ => (x : ℂ) ^ n * H x) := by
      simpa only [Complex.real_smul, Complex.ofReal_pow] using hpowint n
    calc
      (∫ x : ℝ, x ^ n * h x) =
          (∫ x : ℝ, ((x : ℂ) ^ n * H x).re) := by
            apply integral_congr_ae
            filter_upwards with x
            simp [h, ← Complex.ofReal_pow]
      _ = (∫ x : ℝ, (x : ℂ) ^ n * H x).re := integral_re hint
      _ = 0 := by rw [hcmoment]; norm_num

/-- Once positivity is removed, the Gamma moments do not determine a finite
signed measure.  The displayed density representation also records the signed
integral: its `n`th moment is the Gamma moment plus the final Lebesgue integral. -/
theorem positivity_removed_all_moments_counterexample :
    ∃ (s : SignedMeasure ℝ) (h : ℝ → ℝ),
      Continuous h ∧ Integrable h ∧
      s = gammaProbability.toSignedMeasure + volume.withDensityᵥ h ∧
      s ≠ gammaProbability.toSignedMeasure ∧
      ∀ n : ℕ,
        Integrable (fun x : ℝ => x ^ n * h x) ∧
        (∫ x : ℝ, x ^ n ∂gammaProbability) +
            (∫ x : ℝ, x ^ n * h x) = ((n + 1).factorial : ℝ) := by
  obtain ⟨h, hhcont, hhne, hhint, hhmom⟩ := exists_real_rapid_moment_null
  let s : SignedMeasure ℝ := gammaProbability.toSignedMeasure + volume.withDensityᵥ h
  have hint : Integrable h := by simpa using hhint 0
  have hdensity_ne : volume.withDensityᵥ h ≠ (0 : SignedMeasure ℝ) := by
    intro he
    have hae : h =ᵐ[volume] (0 : ℝ → ℝ) :=
      (hint.withDensityᵥ_eq_iff (integrable_zero ℝ ℝ volume)).mp (by
        change volume.withDensityᵥ h = volume.withDensityᵥ (0 : ℝ → ℝ)
        rw [withDensityᵥ_zero]
        exact he)
    have hzero : h = (0 : ℝ → ℝ) :=
      MeasureTheory.Measure.eq_of_ae_eq hae hhcont continuous_zero
    exact hhne hzero
  refine ⟨s, h, hhcont, hint, rfl, ?_, ?_⟩
  · intro he
    dsimp [s] at he
    have : volume.withDensityᵥ h = (0 : SignedMeasure ℝ) := by
      apply add_left_cancel (a := gammaProbability.toSignedMeasure)
      simpa using he
    exact hdensity_ne this
  · intro n
    refine ⟨hhint n, ?_⟩
    rw [gamma_probability_moments, hhmom, add_zero]

/-- Pairwise separated positive intervals used for the finite-moment perturbation. -/
def cutoffCell (j : ℕ) : Set ℝ :=
  Ioo (2 * (j : ℝ) + 1) (2 * (j : ℝ) + 2)

theorem cutoffCell_measurable (j : ℕ) : MeasurableSet (cutoffCell j) :=
  measurableSet_Ioo

theorem cutoffCell_gamma_pos (j : ℕ) : 0 < gammaProbability (cutoffCell j) := by
  apply (gamma_probability_open_positive_iff _ isOpen_Ioo).2
  refine ⟨2 * (j : ℝ) + 3 / 2, ⟨?_, ?_⟩⟩
  · change 0 < 2 * (j : ℝ) + 3 / 2
    positivity
  · constructor <;> dsimp [cutoffCell] <;> linarith

theorem cutoffCell_disjoint {j k : ℕ} (hjk : j ≠ k) :
    Disjoint (cutoffCell j) (cutoffCell k) := by
  rw [Set.disjoint_left]
  intro x hxj hxk
  rcases lt_or_gt_of_ne hjk with hjk | hkj
  · have hc : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hjk
    dsimp [cutoffCell] at hxj hxk
    rcases hxj with ⟨hxj1, hxj2⟩
    rcases hxk with ⟨hxk1, hxk2⟩
    linarith
  · have hc : (k : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hkj
    dsimp [cutoffCell] at hxj hxk
    rcases hxj with ⟨hxj1, hxj2⟩
    rcases hxk with ⟨hxk1, hxk2⟩
    linarith

/-- The first `m+1` moments of a linear combination of `m+2` disjoint cells. -/
def cutoffMomentMap (m : ℕ) :
    (Fin (m + 2) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ) where
  toFun c n := ∑ j : Fin (m + 2), c j *
    ∫ x : ℝ in cutoffCell j, x ^ (n : ℕ) ∂gammaProbability
  map_add' c d := by
    funext n
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r c := by
    funext n
    simp [mul_assoc, Finset.mul_sum]

theorem cutoffMomentMap_has_nonzero_kernel (m : ℕ) :
    ∃ c : Fin (m + 2) → ℝ, c ≠ 0 ∧ cutoffMomentMap m c = 0 := by
  have hk : LinearMap.ker (cutoffMomentMap m) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simp [Module.finrank_pi_fintype])
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  exact ⟨c, hc0, hc⟩

/-- A bounded step-function perturbation supported on the separated cells. -/
def cutoffPerturbation (m : ℕ) (c : Fin (m + 2) → ℝ) (x : ℝ) : ℝ :=
  ∑ j : Fin (m + 2), (cutoffCell j).indicator (fun _ => c j) x

theorem cutoffPerturbation_measurable (m : ℕ) (c : Fin (m + 2) → ℝ) :
    Measurable (cutoffPerturbation m c) := by
  apply Finset.measurable_sum
  intro j hj
  exact measurable_const.indicator (cutoffCell_measurable j)

theorem cutoffPerturbation_eq_on_cell (m : ℕ) (c : Fin (m + 2) → ℝ)
    (j : Fin (m + 2)) {x : ℝ} (hx : x ∈ cutoffCell j) :
    cutoffPerturbation m c x = c j := by
  rw [cutoffPerturbation, Finset.sum_eq_single j]
  · simp only [Set.indicator_of_mem hx]
  · intro k hk hkj
    have hnat : (k : ℕ) ≠ (j : ℕ) := by
      intro hval
      exact hkj (Fin.ext hval)
    have hnot : x ∉ cutoffCell k := by
      intro hxk
      exact Set.disjoint_left.mp (cutoffCell_disjoint hnat) hxk hx
    simp only [Set.indicator_of_not_mem hnot]
  · simp

theorem cutoffPerturbation_abs_le_sum (m : ℕ) (c : Fin (m + 2) → ℝ) (x : ℝ) :
    |cutoffPerturbation m c x| ≤ ∑ j : Fin (m + 2), |c j| := by
  calc
    |cutoffPerturbation m c x| ≤
        ∑ j : Fin (m + 2), |(cutoffCell j).indicator (fun _ => c j) x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin (m + 2), |c j| := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hx : x ∈ cutoffCell j
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_not_mem hx]

theorem cutoffPerturbation_moment (m : ℕ) (c : Fin (m + 2) → ℝ) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n * cutoffPerturbation m c x) gammaProbability ∧
    (∫ x : ℝ, x ^ n * cutoffPerturbation m c x ∂gammaProbability) =
      ∑ j : Fin (m + 2), c j *
        ∫ x : ℝ in cutoffCell j, x ^ n ∂gammaProbability := by
  have hi (j : Fin (m + 2)) :
      Integrable (fun x : ℝ => x ^ n *
        (cutoffCell j).indicator (fun _ => c j) x) gammaProbability := by
    have hb : IntegrableOn (fun x : ℝ => x ^ n * c j) (cutoffCell j) gammaProbability := by
      simpa only [mul_comm] using
        (gamma_probability_monomial_integrable n).integrableOn.const_mul (c j)
    rw [show (fun x : ℝ => x ^ n *
        (cutoffCell j).indicator (fun _ => c j) x) =
        (cutoffCell j).indicator (fun x => x ^ n * c j) by
          funext x
          by_cases hx : x ∈ cutoffCell j <;>
            simp [Set.indicator_of_mem, Set.indicator_of_not_mem, hx]]
    exact hb.integrable_indicator (cutoffCell_measurable j)
  constructor
  · change Integrable (fun x : ℝ => x ^ n *
      ∑ j : Fin (m + 2), (cutoffCell j).indicator (fun _ => c j) x) gammaProbability
    simpa only [Finset.mul_sum] using integrable_finset_sum _ (fun j _ => hi j)
  · change (∫ x : ℝ, x ^ n *
      (∑ j : Fin (m + 2), (cutoffCell j).indicator (fun _ => c j) x)
        ∂gammaProbability) = _
    rw [show (fun x : ℝ => x ^ n *
        (∑ j : Fin (m + 2), (cutoffCell j).indicator (fun _ => c j) x)) =
        (fun x : ℝ => ∑ j : Fin (m + 2),
          x ^ n * (cutoffCell j).indicator (fun _ => c j) x) by
            funext x
            rw [Finset.mul_sum]]
    rw [integral_finset_sum _ (fun j _ => hi j)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [show (fun x : ℝ => x ^ n * (cutoffCell j).indicator (fun _ => c j) x) =
        (cutoffCell j).indicator (fun x => c j * x ^ n) by
          funext x
          by_cases hx : x ∈ cutoffCell j <;>
            simp [Set.indicator_of_mem, Set.indicator_of_not_mem, hx, mul_comm]]
    rw [integral_indicator (cutoffCell_measurable j), integral_mul_left]

/-- For every finite cutoff there is a bounded measurable nonzero perturbation,
orthogonal to all monomials through that cutoff under the Gamma law. -/
theorem exists_bounded_finite_moment_perturbation (m : ℕ) :
    ∃ q : ℝ → ℝ,
      Measurable q ∧
      (∀ x, |q x| ≤ (1 / 2 : ℝ)) ∧
      ¬q =ᵐ[gammaProbability] (0 : ℝ → ℝ) ∧
      ∀ n : ℕ, n ≤ m →
        Integrable (fun x : ℝ => x ^ n * q x) gammaProbability ∧
        (∫ x : ℝ, x ^ n * q x ∂gammaProbability) = 0 := by
  obtain ⟨c, hcne, hcmap⟩ := cutoffMomentMap_has_nonzero_kernel m
  obtain ⟨j, hcj⟩ : ∃ j : Fin (m + 2), c j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hcne
    funext k
    exact h k
  let C : ℝ := ∑ k : Fin (m + 2), |c k|
  have hCpos : 0 < C := by
    dsimp [C]
    apply Finset.sum_pos'
    · intro k hk
      exact abs_nonneg _
    · exact ⟨j, Finset.mem_univ _, abs_pos.mpr hcj⟩
  let d : Fin (m + 2) → ℝ := fun k => c k / (2 * C)
  let q : ℝ → ℝ := cutoffPerturbation m d
  have hdsmul : d = (1 / (2 * C)) • c := by
    funext k
    dsimp [d]
    change c k / (2 * C) = (1 / (2 * C)) * c k
    ring
  have hdmap : cutoffMomentMap m d = 0 := by
    rw [hdsmul, LinearMap.map_smul, hcmap, smul_zero]
  have hdsum : (∑ k : Fin (m + 2), |d k|) = (1 / 2 : ℝ) := by
    calc
      (∑ k : Fin (m + 2), |d k|) =
          ∑ k : Fin (m + 2), |c k| / (2 * C) := by
            apply Finset.sum_congr rfl
            intro k hk
            dsimp [d]
            rw [abs_div, abs_of_pos (mul_pos (by norm_num) hCpos)]
      _ = C / (2 * C) := by simp only [C, Finset.sum_div]
      _ = 1 / 2 := by
        field_simp [ne_of_gt hCpos]
        ring
  have hqbound : ∀ x, |q x| ≤ (1 / 2 : ℝ) := by
    intro x
    calc
      |q x| ≤ ∑ k : Fin (m + 2), |d k| := cutoffPerturbation_abs_le_sum m d x
      _ = 1 / 2 := hdsum
  have hdjne : d j ≠ 0 := by
    dsimp [d]
    exact div_ne_zero hcj (mul_ne_zero (by norm_num) (ne_of_gt hCpos))
  have hqnae : ¬q =ᵐ[gammaProbability] (0 : ℝ → ℝ) := by
    intro hae
    have hnull : gammaProbability {x | q x ≠ 0} = 0 := by
      simpa only [Pi.zero_apply] using (ae_iff.mp hae)
    have hsubset : cutoffCell j ⊆ {x | q x ≠ 0} := by
      intro x hx
      change q x ≠ 0
      rw [show q x = d j by exact cutoffPerturbation_eq_on_cell m d j hx]
      exact hdjne
    have hz := measure_mono_null hsubset hnull
    exact (ne_of_gt (cutoffCell_gamma_pos j)) hz
  refine ⟨q, cutoffPerturbation_measurable m d, hqbound, hqnae, ?_⟩
  intro n hn
  have hmom := cutoffPerturbation_moment m d n
  refine ⟨hmom.1, ?_⟩
  rw [hmom.2]
  have hnfin : n < m + 1 := Nat.lt_succ_iff.mpr hn
  exact congrFun hdmap ⟨n, hnfin⟩

/-- Retaining any prescribed finite initial segment of the ordinary moments
does not identify the Gamma law, even among positive probability measures. -/
theorem finite_moments_do_not_identify_gamma (m : ℕ) :
    ∃ μ : Measure ℝ,
      IsProbabilityMeasure μ ∧ μ ≠ gammaProbability ∧
      ∀ n : ℕ, n ≤ m →
        Integrable (fun x : ℝ => x ^ n) μ ∧
        (∫ x : ℝ, x ^ n ∂μ) = ((n + 1).factorial : ℝ) := by
  obtain ⟨q, hqmeas, hqbound, hqnae, hqmom⟩ :=
    exists_bounded_finite_moment_perturbation m
  have hqnonneg (x : ℝ) : 0 ≤ 1 + q x := by
    have hlow : -(1 / 2 : ℝ) ≤ q x := neg_le_of_abs_le (hqbound x)
    linarith
  let w : ℝ → ℝ≥0 := fun x => ⟨1 + q x, hqnonneg x⟩
  have hwmeas : Measurable w := by
    apply Measurable.subtype_mk
    exact measurable_const.add hqmeas
  let μ : Measure ℝ := gammaProbability.withDensity (fun x => (w x : ℝ≥0∞))
  have hq0 := hqmom 0 (Nat.zero_le m)
  have hqint : Integrable q gammaProbability := by simpa using hq0.1
  have hqzero : (∫ x : ℝ, q x ∂gammaProbability) = 0 := by simpa using hq0.2
  have honeint : Integrable (fun _ : ℝ => (1 : ℝ)) gammaProbability := by simp
  have hwint : Integrable (fun x : ℝ => (w x : ℝ)) gammaProbability := by
    simpa only [w, NNReal.coe_mk] using honeint.add hqint
  have hwintegral : (∫ x : ℝ, (w x : ℝ) ∂gammaProbability) = 1 := by
    change (∫ x : ℝ, 1 + q x ∂gammaProbability) = 1
    rw [integral_add honeint hqint, hqzero]
    simp
  have hμuniv : μ univ = 1 := by
    change (gammaProbability.withDensity (fun x => (w x : ℝ≥0∞))) univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [lintegral_coe_eq_integral w hwint, hwintegral]
    norm_num
  let hμprob : IsProbabilityMeasure μ := IsProbabilityMeasure.mk hμuniv
  have hμne : μ ≠ gammaProbability := by
    intro heq
    letI : IsProbabilityMeasure μ := hμprob
    have hlin : (∫⁻ x : ℝ, (w x : ℝ≥0∞) ∂gammaProbability) ≠ ∞ := by
      rw [lintegral_coe_eq_integral w hwint, hwintegral]
      norm_num
    have hvw : gammaProbability.withDensityᵥ (fun x => (w x : ℝ)) =
        μ.toSignedMeasure := by
      have hh := withDensityᵥ_toReal
        (μ := gammaProbability) hwmeas.coe_nnreal_ennreal.aemeasurable hlin
      simpa only [ENNReal.coe_toReal, μ] using hh
    have hvone : gammaProbability.withDensityᵥ (fun _ : ℝ => (1 : ℝ)) =
        gammaProbability.toSignedMeasure := by
      have hh := withDensityᵥ_toReal
        (μ := gammaProbability) (measurable_const : Measurable (fun _ : ℝ => (1 : ℝ≥0∞))).aemeasurable
        (by simp)
      simpa using hh
    have hv : gammaProbability.withDensityᵥ (fun x => (w x : ℝ)) =
        gammaProbability.withDensityᵥ (fun _ : ℝ => (1 : ℝ)) := by
      calc
        gammaProbability.withDensityᵥ (fun x => (w x : ℝ)) = μ.toSignedMeasure := hvw
        _ = gammaProbability.toSignedMeasure := Measure.toSignedMeasure_congr heq
        _ = gammaProbability.withDensityᵥ (fun _ : ℝ => (1 : ℝ)) := hvone.symm
    have hae : (fun x : ℝ => (w x : ℝ)) =ᵐ[gammaProbability]
        (fun _ : ℝ => (1 : ℝ)) :=
      hwint.ae_eq_of_withDensityᵥ_eq honeint hv
    apply hqnae
    filter_upwards [hae] with x hx
    change q x = 0
    change 1 + q x = 1 at hx
    linarith
  refine ⟨μ, hμprob, hμne, ?_⟩
  intro n hn
  have hpert := hqmom n hn
  have hbase := gamma_probability_monomial_integrable n
  have hweighted : Integrable (fun x : ℝ => w x • x ^ n) gammaProbability := by
    have hadd := hbase.add hpert.1
    convert hadd using 1
    funext x
    change (w x : ℝ) * x ^ n = x ^ n + x ^ n * q x
    change (1 + q x) * x ^ n = _
    ring
  constructor
  · exact (integrable_withDensity_iff_integrable_smul hwmeas).2 hweighted
  · change (∫ x : ℝ, x ^ n ∂gammaProbability.withDensity
        (fun x => (w x : ℝ≥0∞))) = _
    rw [integral_withDensity_eq_integral_smul hwmeas]
    rw [show (fun x : ℝ => w x • x ^ n) =
        (fun x : ℝ => x ^ n + x ^ n * q x) by
          funext x
          change (w x : ℝ) * x ^ n = _
          change (1 + q x) * x ^ n = _
          ring]
    rw [integral_add hbase hpert.1, gamma_probability_moments, hpert.2, add_zero]

end
end Sigma
