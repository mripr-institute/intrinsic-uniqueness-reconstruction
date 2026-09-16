import SigmaZeros
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace Sigma
noncomputable section
open Filter Set MeasureTheory
open scoped Topology BigOperators

def zeroFamilyConstant (k : ℝ) : ℝ := (k-1)*k^k
def zeroFamily (k t : ℝ) : ℝ := zeroFamilyConstant k*t*(t+k)^(-(k+1))
def zeroFamilyRising (k : ℝ) (n : ℕ) : ℝ := ∏ i ∈ Finset.range n, (k+(i : ℝ))
def zeroFamilyDerivative (k : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (-1 : ℝ)^n*zeroFamilyConstant k*zeroFamilyRising k n*(t-n)*(t+k)^(-(k+n+1))

theorem zeroFamilyConstant_positive {k : ℝ} (hk : 1 < k) : 0 < zeroFamilyConstant k :=
  mul_pos (sub_pos.mpr hk) (Real.rpow_pos_of_pos (by linarith) _)

theorem zeroFamily_positive {k t : ℝ} (hk : 1 < k) (ht : 0 < t) :
    0 < zeroFamily k t := by
  exact mul_pos (mul_pos (zeroFamilyConstant_positive hk) ht)
    (Real.rpow_pos_of_pos (by linarith) _)

theorem zeroFamilyRising_positive {k : ℝ} (hk : 0 < k) (n : ℕ) :
    0 < zeroFamilyRising k n := by
  exact Finset.prod_pos fun i _ => add_pos_of_pos_of_nonneg hk (Nat.cast_nonneg i)

theorem zeroFamilyRising_succ (k : ℝ) (n : ℕ) :
    zeroFamilyRising k (n+1) = zeroFamilyRising k n*(k+n) := by
  exact Finset.prod_range_succ (fun i => k+(i : ℝ)) n

theorem zeroFamilyDerivative_zero (k t : ℝ) : zeroFamilyDerivative k 0 t = zeroFamily k t := by
  simp [zeroFamilyDerivative, zeroFamilyRising, zeroFamily]

theorem zeroFamily_step (k : ℝ) (n : ℕ) {t : ℝ} (ht : 0 < t+k) :
    HasDerivAt (zeroFamilyDerivative k n) (zeroFamilyDerivative k (n+1) t) t := by
  have hr := ((hasDerivAt_id t).add_const k).rpow_const (p := -(k+n+1))
    (Or.inl (ne_of_gt ht))
  have hd := (((hasDerivAt_id t).sub_const (n : ℝ)).mul hr).const_mul
    ((-1 : ℝ)^n*zeroFamilyConstant k*zeroFamilyRising k n)
  have he : (t+k)^(-(k+(n : ℝ)+1)) = (t+k)^(-(k+(n : ℝ)+2))*(t+k) := by
    rw [← Real.rpow_add_one (ne_of_gt ht)]
    congr 1
    ring
  convert hd using 1
  · funext x
    unfold zeroFamilyDerivative
    simp only [id_eq]
    ring
  · simp only [zeroFamilyDerivative, zeroFamilyRising_succ, pow_succ, Nat.cast_add,
      Nat.cast_one, id_eq, one_mul]
    rw [he, show -(k+(n : ℝ)+1)-1 = -(k+(n : ℝ)+2) by ring]
    ring

theorem zeroFamily_iteratedDeriv (k : ℝ) (n : ℕ) :
    ∀ t, 0 < t+k → iteratedDeriv n (zeroFamily k) t = zeroFamilyDerivative k n t := by
  induction n with
  | zero => intro t ht; simpa using (zeroFamilyDerivative_zero k t).symm
  | succ n ih =>
    intro t ht
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv n (zeroFamily k) =ᶠ[𝓝 t] zeroFamilyDerivative k n := by
      have ho : IsOpen {x : ℝ | 0 < x+k} := isOpen_lt continuous_const (continuous_id.add continuous_const)
      filter_upwards [ho.mem_nhds ht] with x hx
      exact ih x hx
    exact ((zeroFamily_step k n ht).congr_of_eventuallyEq he).deriv

theorem zeroFamily_exact_zeros {k : ℝ} (hk : 1 < k) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv n (zeroFamily k) t = 0 ↔ t = n := by
  rw [zeroFamily_iteratedDeriv k n t (by linarith)]
  have hC := ne_of_gt (zeroFamilyConstant_positive hk)
  have hR := ne_of_gt (zeroFamilyRising_positive (by linarith : 0 < k) n)
  have hp := ne_of_gt (Real.rpow_pos_of_pos (by linarith : 0 < t+k) (-(k+n+1)))
  simp only [zeroFamilyDerivative, mul_eq_zero, hC, hR, hp,
    pow_ne_zero n (by norm_num : (-1 : ℝ) ≠ 0), false_or, or_false, sub_eq_zero]

def zeroFamilyPrimitive (k t : ℝ) : ℝ :=
  zeroFamilyConstant k*((t+k)^(-k)-(t+k)^(1-k)/(k-1))

theorem zeroFamilyPrimitive_deriv {k t : ℝ} (hk : 1 < k) (ht : 0 ≤ t) :
    HasDerivAt (zeroFamilyPrimitive k) (zeroFamily k t) t := by
  have hp : 0 < t+k := by linarith
  have h1 := ((hasDerivAt_id t).add_const k).rpow_const (p := -k) (Or.inl (ne_of_gt hp))
  have h2 := (((hasDerivAt_id t).add_const k).rpow_const (p := 1-k)
    (Or.inl (ne_of_gt hp))).div_const (k-1)
  have hd := (h1.sub h2).const_mul (zeroFamilyConstant k)
  have he : (t+k)^(-k) = (t+k)^(-(k+1))*(t+k) := by
    rw [← Real.rpow_add_one (ne_of_gt hp)]
    congr 1
    ring
  convert hd using 1
  simp only [zeroFamily, id_eq, mul_one]
  rw [show -k-1 = -(k+1) by ring, show 1-k-1 = -k by ring, he]
  field_simp [ne_of_gt (sub_pos.mpr hk)]
  ring

theorem zeroFamilyPrimitive_limit {k : ℝ} (hk : 1 < k) :
    Tendsto (zeroFamilyPrimitive k) atTop (𝓝 0) := by
  have hc : Tendsto (fun t : ℝ => t+k) atTop atTop := tendsto_atTop_add_const_right _ k tendsto_id
  have h1 := (tendsto_rpow_neg_atTop (by linarith : 0 < k)).comp hc
  have h2 := (tendsto_rpow_neg_atTop (by linarith : 0 < k-1)).comp hc
  have hd := (h1.sub (h2.div_const (k-1))).const_mul (zeroFamilyConstant k)
  convert hd using 1
  · funext t
    simp only [zeroFamilyPrimitive, Function.comp_def, neg_sub]
  · simp

theorem zeroFamily_integrable {k : ℝ} (hk : 1 < k) :
    IntegrableOn (zeroFamily k) (Ioi 0) := by
  exact integrableOn_Ioi_deriv_of_nonneg'
    (fun t ht => zeroFamilyPrimitive_deriv hk ht)
    (fun t ht => (zeroFamily_positive hk ht).le) (zeroFamilyPrimitive_limit hk)

theorem zeroFamily_mass_one {k : ℝ} (hk : 1 < k) :
    (∫ t in Ioi (0 : ℝ), zeroFamily k t) = 1 := by
  have hi := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun t ht => zeroFamilyPrimitive_deriv hk ht)
    (fun t ht => (zeroFamily_positive hk ht).le) (zeroFamilyPrimitive_limit hk)
  have hp : 0 < k := by linarith
  have he : k^(1-k) = k^(-k)*k := by
    rw [← Real.rpow_add_one (ne_of_gt hp)]
    congr 1
    ring
  have hn : k^k*k^(-k) = 1 := by rw [← Real.rpow_add hp]; simp
  rw [hi]
  simp only [zeroFamilyPrimitive, zeroFamilyConstant, zero_add]
  rw [he]
  calc
    _ = k^k*k^(-k) := by field_simp [ne_of_gt (sub_pos.mpr hk)]; ring
    _ = 1 := hn

theorem zeroFamily_formula (k t : ℝ) (ht : 0 ≤ t+k) :
    zeroFamily k t = (k-1)*k^k*t/(t+k)^(k+1) := by
  unfold zeroFamily zeroFamilyConstant
  rw [Real.rpow_neg ht]
  rfl

theorem zeroFamily_simple_zeros {k : ℝ} (hk : 1 < k) (n : ℕ) (hn : 0 < n) :
    iteratedDeriv n (zeroFamily k) n = 0 ∧
    deriv (iteratedDeriv n (zeroFamily k)) n ≠ 0 := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨(zeroFamily_exact_zeros hk n hp).mpr rfl, ?_⟩
  rw [← iteratedDeriv_succ]
  intro hz
  have he := (zeroFamily_exact_zeros hk (n+1) hp).mp hz
  push_cast at he
  linarith

theorem zeroFamily_tendsto_zero {k : ℝ} (hk : 1 < k) :
    Tendsto (zeroFamily k) (𝓝 0) (𝓝 0) := by
  have hd : HasDerivAt (zeroFamily k) (zeroFamilyDerivative k 1 0) 0 := by
    have he : zeroFamilyDerivative k 0 = zeroFamily k := funext (zeroFamilyDerivative_zero k)
    simpa only [he] using zeroFamily_step k 0 (by linarith : 0 < (0 : ℝ)+k)
  have hc : Tendsto (zeroFamily k) (𝓝 0) (𝓝 (zeroFamily k 0)) := hd.continuousAt
  simpa only [zeroFamily, mul_zero, zero_mul] using hc

theorem zeroFamily_tendsto_infinity {k : ℝ} (hk : 1 < k) :
    Tendsto (zeroFamily k) atTop (𝓝 0) := by
  have hc : Tendsto (fun t : ℝ => t+k) atTop atTop := tendsto_atTop_add_const_right _ k tendsto_id
  have h1 := (tendsto_rpow_neg_atTop (by linarith : 0 < k)).comp hc
  have h2 := (tendsto_rpow_neg_atTop (by linarith : 0 < k+1)).comp hc
  have hd := (h1.sub (h2.const_mul k)).const_mul (zeroFamilyConstant k)
  have hz : Tendsto (fun t : ℝ => zeroFamilyConstant k*((t+k)^(-k)-k*(t+k)^(-(k+1))))
      atTop (𝓝 0) := by simpa only [Function.comp_def, mul_zero, sub_zero] using hd
  apply hz.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have he : (t+k)^(-k) = (t+k)^(-(k+1))*(t+k) := by
    rw [← Real.rpow_add_one (by linarith : t+k ≠ 0)]
    congr 1
    ring
  rw [he]
  unfold zeroFamily
  ring

theorem zeroFamily_second_mode_ratio {k : ℝ} (hk : 1 < k) :
    (k+1)*iteratedDeriv 2 (zeroFamily k) 1 = -k*zeroFamily k 1 := by
  rw [zeroFamily_iteratedDeriv k 2 1 (by linarith)]
  have hp : 0 < 1+k := by linarith
  have he : (1+k)^(-(k+1)) = (1+k)^(-(k+3))*(1+k)^2 := by
    rw [← Real.rpow_two, ← Real.rpow_add hp]
    congr 1
    ring
  have hR : zeroFamilyRising k 2 = k*(k+1) := by
    norm_num [zeroFamilyRising, Finset.prod_range_succ]
  simp only [zeroFamilyDerivative, zeroFamily, hR, Nat.cast_ofNat, neg_one_sq,
    one_mul, mul_one]
  rw [show k+2+1 = k+3 by ring]
  rw [he]
  ring

theorem zeroFamily_not_gamma {k : ℝ} (hk : 1 < k) :
    ¬ ∀ t > 0, zeroFamily k t = p t := by
  intro he
  have h1 : ∀ t > 0, deriv (zeroFamily k) t = deriv p t := by
    intro t ht
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
    exact he x hx
  have h2 : iteratedDeriv 2 (zeroFamily k) 1 = iteratedDeriv 2 p 1 := by
    simp only [iteratedDeriv_succ, iteratedDeriv_zero]
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_Ioi.mem_nhds (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact h1 x hx
  have hm := zeroFamily_second_mode_ratio hk
  rw [h2, gamma_iteratedDeriv, he 1 (by norm_num)] at hm
  norm_num [gammaDerivative, p, SigmaPresentations.density] at hm

end
end Sigma
