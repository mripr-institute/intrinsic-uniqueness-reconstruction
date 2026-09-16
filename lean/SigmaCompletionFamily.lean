import SigmaCompletion

namespace Sigma
noncomputable section
open Filter Set
open scoped Topology

def completionParameter (h : ℝ → ℝ) : ℝ := 1 + deriv h 0

def completionFamily (K z : ℝ) : ℝ :=
  K * Real.log (1 + z) - z - K / 2 * Real.log K

theorem completionFamily_hasDerivAt (K : ℝ) {z : ℝ} (hz : -1 < z) :
    HasDerivAt (completionFamily K) (K / (1 + z) - 1) z := by
  have hp : 1 + z ≠ 0 := by linarith
  convert (((((hasDerivAt_id z).const_add 1).log hp).const_mul K).sub
    (hasDerivAt_id z)).sub_const (K / 2 * Real.log K) using 1
  simp only [id_eq]
  ring

theorem completionFamily_derivative (K : ℝ) {z : ℝ} (hz : -1 < z) :
    deriv (completionFamily K) z = K / (1 + z) - 1 := (completionFamily_hasDerivAt K hz).deriv

theorem completionFamily_derivative_range {K z : ℝ} (hK : 0 < K) (hz : -1 < z) :
    -1 < deriv (completionFamily K) z := by
  rw [completionFamily_derivative K hz]
  have hp := div_pos hK (show 0 < 1 + z by linarith)
  linarith

theorem completionFamily_typed_equation {K : ℝ} (hK : 0 < K) :
    TypedCompletion (completionFamily K) := by
  intro z hz
  have hp : 0 < 1 + z := by linarith
  rw [completionFamily_derivative K hz]
  unfold completionEll completionFamily
  rw [show 1 + (K / (1 + z) - 1) = K / (1 + z) by ring,
    Real.log_div (ne_of_gt hK) (ne_of_gt hp)]
  ring

theorem completionParameter_positive (h : ℝ → ℝ)
    (hr : ∀ z > -1, -1 < deriv h z) : 0 < completionParameter h := by
  have hh := hr 0 (by norm_num)
  unfold completionParameter
  linarith

/-- The product determining K is derived from the actual second derivative. -/
theorem completion_product_constant (h : ℝ → ℝ)
    (hd : ∀ z > -1, DifferentiableAt ℝ h z)
    (hr : ∀ z > -1, -1 < deriv h z) (he : TypedCompletion h) :
    ∀ t > 0, t * (1 + deriv h (t - 1)) = completionParameter h := by
  have hp : ∀ t > 0, HasDerivAt (fun t : ℝ => t * (1 + deriv h (t - 1))) 0 t := by
    intro t ht
    have hq := (completion_second_hasDerivAt h hd hr he (show -1 < t - 1 by linarith)).comp t
      ((hasDerivAt_id t).sub_const 1)
    have hh := (hasDerivAt_id t).mul (hq.const_add 1)
    convert hh using 1
    simp only [id_eq]
    field_simp
    <;> ring
  apply equal_of_equal_derivatives _ (fun _ => completionParameter h)
    (fun t ht => (hp t ht).differentiableAt)
    (fun t _ => (hasDerivAt_const t (completionParameter h)).differentiableAt)
  · intro t ht
    rw [(hp t ht).deriv]
    simp
  · simp [completionParameter]

theorem completion_derivative_formula (h : ℝ → ℝ)
    (hd : ∀ z > -1, DifferentiableAt ℝ h z)
    (hr : ∀ z > -1, -1 < deriv h z) (he : TypedCompletion h) :
    ∀ z > -1, deriv h z = completionParameter h / (1 + z) - 1 := by
  intro z hz
  have hh := completion_product_constant h hd hr he (1 + z) (by linarith)
  rw [show 1 + z - 1 = z by ring] at hh
  apply (eq_sub_iff_add_eq).mpr
  apply (eq_div_iff (show 1 + z ≠ 0 by linarith)).mpr
  nlinarith

theorem completion_primitive_formula (h : ℝ → ℝ)
    (hd : ∀ z > -1, DifferentiableAt ℝ h z)
    (hr : ∀ z > -1, -1 < deriv h z) (he : TypedCompletion h) :
    ∀ z > -1, h z = completionParameter h * Real.log (1 + z) - z + h 0 := by
  have hG : ∀ t > 0, HasDerivAt (fun t : ℝ => h (t - 1))
      (completionParameter h / t - 1) t := by
    intro t ht
    have hh := (hd (t - 1) (by linarith)).hasDerivAt.comp t ((hasDerivAt_id t).sub_const 1)
    rw [completion_derivative_formula h hd hr he (t - 1) (by linarith)] at hh
    simpa using hh
  have hT : ∀ t > 0, HasDerivAt
      (fun t : ℝ => completionParameter h * Real.log t - (t - 1) + h 0)
      (completionParameter h / t - 1) t := by
    intro t ht
    convert (((Real.hasDerivAt_log (ne_of_gt ht)).const_mul (completionParameter h)).sub
      ((hasDerivAt_id t).sub_const 1)).add_const (h 0) using 1
  have hident : ∀ t > 0, h (t - 1) = completionParameter h * Real.log t - (t - 1) + h 0 := by
    apply equal_of_equal_derivatives _ _
      (fun t ht => (hG t ht).differentiableAt)
      (fun t ht => (hT t ht).differentiableAt)
    · intro t ht
      rw [(hG t ht).deriv, (hT t ht).deriv]
    · simp
  intro z hz
  simpa using hident (1 + z) (by linarith)

theorem completion_constant_formula (h : ℝ → ℝ)
    (hd : ∀ z > -1, DifferentiableAt ℝ h z)
    (hr : ∀ z > -1, -1 < deriv h z) (he : TypedCompletion h) :
    h 0 = -(completionParameter h / 2 * Real.log (completionParameter h)) := by
  have hh := he 0 (by norm_num)
  unfold completionEll at hh
  rw [completion_primitive_formula h hd hr he (deriv h 0) (hr 0 (by norm_num))] at hh
  change deriv h 0 + (completionParameter h * Real.log (completionParameter h) - deriv h 0 + h 0) =
    -(0 + h 0) at hh
  linarith

theorem completion_identified_family (h : ℝ → ℝ)
    (hd : ∀ z > -1, DifferentiableAt ℝ h z)
    (hr : ∀ z > -1, -1 < deriv h z) (he : TypedCompletion h) :
    ∀ z > -1, h z = completionFamily (completionParameter h) z := by
  intro z hz
  rw [completion_primitive_formula h hd hr he z hz, completion_constant_formula h hd hr he]
  rfl

/-- Exact final:C3-completion iff under only its stated differentiability and range conditions. -/
theorem typed_completion_iff_family (h : ℝ → ℝ)
    (hd : ∀ z > -1, DifferentiableAt ℝ h z)
    (hr : ∀ z > -1, -1 < deriv h z) :
    TypedCompletion h ↔ ∃ K : ℝ, 0 < K ∧ ∀ z > -1, h z = completionFamily K z := by
  constructor
  · intro he
    exact ⟨completionParameter h, completionParameter_positive h hr, completion_identified_family h hd hr he⟩
  · rintro ⟨K, hK, hv⟩ z hz
    have hD : deriv h z = deriv (completionFamily K) z := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
      exact hv y hy
    unfold completionEll
    rw [hv (deriv h z) (hr z hz), hv z hz, hD]
    exact completionFamily_typed_equation hK z hz

theorem completionFamily_zero (K : ℝ) :
    completionFamily K 0 = -(K / 2 * Real.log K) := by simp [completionFamily]

theorem completionFamily_derivative_zero (K : ℝ) :
    deriv (completionFamily K) 0 = K - 1 := by
  rw [completionFamily_derivative K (by norm_num)]
  simp

theorem completionFamily_anchors_select_one {K : ℝ} (hK : 0 < K) :
    (completionFamily K 0 = 0 ↔ K = 1) ∧
    (deriv (completionFamily K) 0 = 0 ↔ K = 1) := by
  constructor
  · rw [completionFamily_zero]
    constructor
    · intro hh
      have hm : K * Real.log K = 0 := by nlinarith
      have hl := (mul_eq_zero.mp hm).resolve_left (ne_of_gt hK)
      exact Real.log_injOn_pos hK (by norm_num) (by simpa using hl)
    · intro hh
      simp [hh]
  · rw [completionFamily_derivative_zero, sub_eq_zero]

theorem completion_value_anchor_identifies (h : ℝ → ℝ)
    (hd : ∀ z > -1, DifferentiableAt ℝ h z)
    (hr : ∀ z > -1, -1 < deriv h z) (he : TypedCompletion h) (hv : h 0 = 0) :
    ∀ z > -1, h z = Real.log (1 + z) - z := by
  have hK := completionParameter_positive h hr
  have hform := completion_identified_family h hd hr he
  have h0 := hform 0 (by norm_num)
  have hk : completionParameter h = 1 :=
    (completionFamily_anchors_select_one hK).1.mp (by rw [← h0, hv])
  intro z hz
  simpa [hk, completionFamily] using hform z hz

theorem completion_slope_anchor_identifies (h : ℝ → ℝ)
    (hd : ∀ z > -1, DifferentiableAt ℝ h z)
    (hr : ∀ z > -1, -1 < deriv h z) (he : TypedCompletion h) (hv : deriv h 0 = 0) :
    ∀ z > -1, h z = Real.log (1 + z) - z := by
  have hk : completionParameter h = 1 := by simp [completionParameter, hv]
  intro z hz
  simpa [hk, completionFamily] using completion_identified_family h hd hr he z hz

/-- The last clause of final:C3-completion: injectivity and the genuine
second differentiability are consequences, not candidate assumptions. -/
theorem completion_derived_regularity (h : ℝ → ℝ)
    (hd : ∀ z > -1, DifferentiableAt ℝ h z)
    (hr : ∀ z > -1, -1 < deriv h z) (he : TypedCompletion h) :
    InjOn (completionEll h) (Ioi (-1)) ∧
      ∀ z > -1, DifferentiableAt ℝ (deriv h) z := by
  exact ⟨(completionEll_strictMono h hd hr).injOn,
    fun _ hz => (completion_second_hasDerivAt h hd hr he hz).differentiableAt⟩

end
end Sigma
