import SigmaOpMarkedCoordinate
import SigmaOpMoments

namespace Sigma
noncomputable section
open MeasureTheory Set
open scoped ENNReal

def coordinateRecoveryKernel (a t : ℝ) : ℝ := (1 + (t - a)^2)⁻¹

theorem coordinate_recovery_kernel_pos (a t : ℝ) :
    0 < coordinateRecoveryKernel a t := by unfold coordinateRecoveryKernel; positivity

theorem coordinate_recovery_kernel_le_one (a t : ℝ) :
    coordinateRecoveryKernel a t ≤ 1 := by
  unfold coordinateRecoveryKernel
  exact (inv_le_one₀ (by positivity)).mpr (by nlinarith [sq_nonneg (t-a)])

theorem coordinate_recovery_skew_bound (a t : ℝ) :
    |(t-a) * coordinateRecoveryKernel a t| ≤ 1 := by
  rw [abs_mul, abs_of_pos (coordinate_recovery_kernel_pos a t)]
  change |t-a| / (1+(t-a)^2) ≤ 1
  apply (div_le_one (by positivity)).mpr
  nlinarith [sq_nonneg (|t-a|-1), sq_abs (t-a)]

theorem coordinate_recovery_quadratic_bound (a t : ℝ) :
    |(t-a)^2 * coordinateRecoveryKernel a t| ≤ 1 := by
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (coordinate_recovery_kernel_pos a t).le)]
  change (t-a)^2 / (1+(t-a)^2) ≤ 1
  exact (div_le_one (by positivity)).mpr (by linarith)

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
private theorem real_bounded_mul_mem (b : ℝ → ℝ) (hb : Measurable b)
    (C : ℝ) (hC : ∀ t, |b t| ≤ C) (f : Lp ℂ 2 μ) :
    Memℒp (fun t : ℝ => (b t : ℂ) * (f : ℝ → ℂ) t) 2 μ := by
  apply (Lp.memℒp f).of_le_mul (c := C)
    ((Complex.measurable_ofReal.comp hb).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable f))
  filter_upwards with t
  simpa only [Pi.mul_apply, Function.comp_apply, norm_mul, Complex.norm_real,
    Real.norm_eq_abs] using
    mul_le_mul_of_nonneg_right (hC t) (norm_nonneg ((f : ℝ → ℂ) t))

private theorem recovery_mem (a : ℝ) (f : Lp ℂ 2 μ) :
    Memℒp (fun t => (coordinateRecoveryKernel a t : ℂ) * (f : ℝ → ℂ) t) 2 μ := by
  apply real_bounded_mul_mem μ _ (by unfold coordinateRecoveryKernel; fun_prop) 1
  intro t
  rw [abs_of_pos (coordinate_recovery_kernel_pos a t)]
  exact coordinate_recovery_kernel_le_one a t

def coordinateRecoveryVector (a : ℝ) (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (recovery_mem μ a f).toLp
    (fun t => (coordinateRecoveryKernel a t : ℂ) * (f : ℝ → ℂ) t)

theorem coordinate_recovery_vector_coe (a : ℝ) (f : Lp ℂ 2 μ) :
    (coordinateRecoveryVector μ a f : ℝ → ℂ) =ᵐ[μ]
      fun t => (coordinateRecoveryKernel a t : ℂ) * (f : ℝ → ℂ) t :=
  (recovery_mem μ a f).coeFn_toLp

private theorem skew_mem (a : ℝ) (f : Lp ℂ 2 μ) :
    Memℒp (fun t => ((t-a)*coordinateRecoveryKernel a t : ℝ) *
      (f : ℝ → ℂ) t) 2 μ :=
  real_bounded_mul_mem μ _ (by unfold coordinateRecoveryKernel; fun_prop) 1
    (coordinate_recovery_skew_bound a) f

def coordinateRecoverySkewVector (a : ℝ) (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (skew_mem μ a f).toLp
    (fun t => (((t-a)*coordinateRecoveryKernel a t : ℝ) : ℂ) * (f : ℝ → ℂ) t)

theorem coordinate_recovery_skew_vector_coe (a : ℝ) (f : Lp ℂ 2 μ) :
    (coordinateRecoverySkewVector μ a f : ℝ → ℂ) =ᵐ[μ]
      fun t => (((t-a)*coordinateRecoveryKernel a t : ℝ) : ℂ) * (f : ℝ → ℂ) t :=
  (skew_mem μ a f).coeFn_toLp

theorem coordinate_recovery_vector_domain (a : ℝ) (f : Lp ℂ 2 μ) :
    coordinateRecoveryVector μ a f ∈ (coordinateMultiplicationOperator μ).domain := by
  change Memℒp (fun t : ℝ => (t : ℂ) * (coordinateRecoveryVector μ a f : ℝ → ℂ) t) 2 μ
  apply (memℒp_congr_ae ?_).mpr
    ((skew_mem μ a f).add ((recovery_mem μ a f).const_mul (a : ℂ)))
  filter_upwards [coordinate_recovery_vector_coe μ a f] with t ht
  simp only [ht, Pi.add_apply]
  push_cast
  ring

theorem coordinate_recovery_skew_vector_domain (a : ℝ) (f : Lp ℂ 2 μ) :
    coordinateRecoverySkewVector μ a f ∈ (coordinateMultiplicationOperator μ).domain := by
  have hq := real_bounded_mul_mem μ (fun t => (t-a)^2 * coordinateRecoveryKernel a t)
    (by unfold coordinateRecoveryKernel; fun_prop) 1 (coordinate_recovery_quadratic_bound a) f
  change Memℒp (fun t : ℝ => (t : ℂ) * (coordinateRecoverySkewVector μ a f : ℝ → ℂ) t) 2 μ
  apply (memℒp_congr_ae ?_).mpr (hq.add ((skew_mem μ a f).const_mul (a : ℂ)))
  filter_upwards [coordinate_recovery_skew_vector_coe μ a f] with t ht
  simp only [ht, Pi.add_apply]
  push_cast
  ring

theorem coordinate_multiplication_coe (f : Lp ℂ 2 μ)
    (hf : f ∈ (coordinateMultiplicationOperator μ).domain) :
    (coordinateMultiplicationOperator μ ⟨f, hf⟩ : ℝ → ℂ) =ᵐ[μ]
      fun t => (t : ℂ) * (f : ℝ → ℂ) t := hf.coeFn_toLp

theorem coordinate_recovery_vector_action (a : ℝ) (f : Lp ℂ 2 μ) :
    coordinateMultiplicationOperator μ
        ⟨coordinateRecoveryVector μ a f, coordinate_recovery_vector_domain μ a f⟩ =
      coordinateRecoverySkewVector μ a f + (a : ℂ) • coordinateRecoveryVector μ a f := by
  apply Lp.ext
  filter_upwards [coordinate_multiplication_coe μ _ (coordinate_recovery_vector_domain μ a f),
    coordinate_recovery_vector_coe μ a f, coordinate_recovery_skew_vector_coe μ a f,
    Lp.coeFn_add (coordinateRecoverySkewVector μ a f) ((a : ℂ) • coordinateRecoveryVector μ a f),
    Lp.coeFn_smul (a : ℂ) (coordinateRecoveryVector μ a f)] with t hm hg hh hadd hsmul
  simp only [hm, hadd, Pi.add_apply, hsmul, Pi.smul_apply, smul_eq_mul, hg, hh]
  push_cast
  ring

theorem coordinate_recovery_skew_vector_action (a : ℝ) (f : Lp ℂ 2 μ) :
    coordinateMultiplicationOperator μ
        ⟨coordinateRecoverySkewVector μ a f, coordinate_recovery_skew_vector_domain μ a f⟩ =
      f - coordinateRecoveryVector μ a f + (a : ℂ) • coordinateRecoverySkewVector μ a f := by
  apply Lp.ext
  filter_upwards [coordinate_multiplication_coe μ _ (coordinate_recovery_skew_vector_domain μ a f),
    coordinate_recovery_vector_coe μ a f, coordinate_recovery_skew_vector_coe μ a f,
    Lp.coeFn_add (f - coordinateRecoveryVector μ a f) ((a : ℂ) • coordinateRecoverySkewVector μ a f),
    Lp.coeFn_sub f (coordinateRecoveryVector μ a f),
    Lp.coeFn_smul (a : ℂ) (coordinateRecoverySkewVector μ a f)] with t hm hg hh hadd hsub hsmul
  simp only [hm, hadd, Pi.add_apply, hsub, Pi.sub_apply, hsmul,
    Pi.smul_apply, smul_eq_mul, hg, hh, coordinateRecoveryKernel]
  push_cast
  have hd : (1 : ℂ) + ((t : ℂ) - (a : ℂ))^2 ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < 1 + (t-a)^2 by positivity))
  field_simp
  <;> ring

/-- Only literal multiplication-domain transport and action are retained. -/
def CoordinateMultiplicationIntertwines (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν) : Prop :=
  ∀ (f : Lp ℂ 2 μ) (hf : f ∈ (coordinateMultiplicationOperator μ).domain),
    ∃ hf' : U f ∈ (coordinateMultiplicationOperator ν).domain,
      U (coordinateMultiplicationOperator μ ⟨f, hf⟩) =
        coordinateMultiplicationOperator ν ⟨U f, hf'⟩

/-- Intertwining the maximal unbounded coordinate operator forces
intertwining of each bounded quadratic resolvent, without any moment bound. -/
theorem coordinate_recovery_vector_intertwines
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν)
    (hU : CoordinateMultiplicationIntertwines μ ν U)
    (a : ℝ) (f : Lp ℂ 2 μ) :
    U (coordinateRecoveryVector μ a f) = coordinateRecoveryVector ν a (U f) := by
  let g := coordinateRecoveryVector μ a f
  let h := coordinateRecoverySkewVector μ a f
  obtain ⟨hdg, heg⟩ := hU g (coordinate_recovery_vector_domain μ a f)
  obtain ⟨hdh, heh⟩ := hU h (coordinate_recovery_skew_vector_domain μ a f)
  have hg : coordinateMultiplicationOperator ν ⟨U g, hdg⟩ = U h + (a : ℂ) • U g := by
    rw [← heg, coordinate_recovery_vector_action, map_add, _root_.map_smul]
  have hh : coordinateMultiplicationOperator ν ⟨U h, hdh⟩ =
      U f - U g + (a : ℂ) • U h := by
    rw [← heh, coordinate_recovery_skew_vector_action, map_add, map_sub, _root_.map_smul]
  have hgc := coordinate_multiplication_coe ν (U g) hdg
  have hhc := coordinate_multiplication_coe ν (U h) hdh
  rw [hg] at hgc
  rw [hh] at hhc
  apply Lp.ext
  filter_upwards [hgc, hhc,
    Lp.coeFn_add (U h) ((a : ℂ) • U g), Lp.coeFn_smul (a : ℂ) (U g),
    Lp.coeFn_add (U f - U g) ((a : ℂ) • U h), Lp.coeFn_sub (U f) (U g),
    Lp.coeFn_smul (a : ℂ) (U h), coordinate_recovery_vector_coe ν a (U f)]
    with t hgc hhc hgadd hgsmul hhadd hhsub hhsmul hres
  simp only [hgadd, Pi.add_apply, hgsmul, Pi.smul_apply, smul_eq_mul] at hgc
  simp only [hhadd, Pi.add_apply, hhsub, Pi.sub_apply, hhsmul,
    Pi.smul_apply, smul_eq_mul] at hhc
  have hgrel : ((t : ℂ)-(a : ℂ)) * (U g : ℝ → ℂ) t = (U h : ℝ → ℂ) t := by
    linear_combination -hgc
  have hhrel : ((t : ℂ)-(a : ℂ)) * (U h : ℝ → ℂ) t =
      (U f : ℝ → ℂ) t - (U g : ℝ → ℂ) t := by
    linear_combination -hhc
  have hall : (1+((t : ℂ)-(a : ℂ))^2) * (U g : ℝ → ℂ) t = (U f : ℝ → ℂ) t := by
    calc
      _ = ((t : ℂ)-(a : ℂ)) * (((t : ℂ)-(a : ℂ)) * (U g : ℝ → ℂ) t) +
          (U g : ℝ → ℂ) t := by ring
      _ = (U f : ℝ → ℂ) t := by rw [hgrel, hhrel]; ring
  change (U g : ℝ → ℂ) t = _
  rw [hres]
  simp only [coordinateRecoveryKernel]
  push_cast
  rw [← hall]
  have hd : (1 : ℂ) + ((t : ℂ) - (a : ℂ))^2 ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < 1 + (t-a)^2 by positivity))
  rw [← mul_assoc, inv_mul_cancel₀ hd, one_mul]

def coordinateRecoveryPower (a : ℝ) : ℕ → Lp ℂ 2 μ
  | 0 => coordinateConstantOne μ
  | n+1 => coordinateRecoveryVector μ a (coordinateRecoveryPower a n)

theorem coordinate_recovery_power_coe (a : ℝ) (n : ℕ) :
    (coordinateRecoveryPower μ a n : ℝ → ℂ) =ᵐ[μ]
      fun t => ((coordinateRecoveryKernel a t)^n : ℝ) := by
  induction n with
  | zero => simpa [coordinateRecoveryPower] using coordinate_constant_one_coe μ
  | succ n ih =>
      filter_upwards [coordinate_recovery_vector_coe μ a (coordinateRecoveryPower μ a n), ih]
        with t ht hn
      simpa [coordinateRecoveryPower, hn, pow_succ, mul_comm] using ht

theorem coordinate_recovery_power_inner (a : ℝ) (n : ℕ) :
    @inner ℂ (Lp ℂ 2 μ) _ (coordinateConstantOne μ) (coordinateRecoveryPower μ a n) =
      Complex.ofReal (∫ t : ℝ, coordinateRecoveryKernel a t ^ n ∂μ) := by
  rw [L2.inner_def]
  calc
    _ = ∫ t : ℝ, ((coordinateRecoveryKernel a t ^ n : ℝ) : ℂ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [coordinate_constant_one_coe μ, coordinate_recovery_power_coe μ a n]
        with t hone hp
      simp [hone, hp, RCLike.inner_apply]
    _ = _ := integral_ofReal

theorem coordinate_recovery_power_intertwines
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν)
    (hU : CoordinateMultiplicationIntertwines μ ν U)
    (hone : U (coordinateConstantOne μ) = coordinateConstantOne ν) (a : ℝ) (n : ℕ) :
    U (coordinateRecoveryPower μ a n) = coordinateRecoveryPower ν a n := by
  induction n with
  | zero => exact hone
  | succ n ih =>
      simp only [coordinateRecoveryPower, coordinate_recovery_vector_intertwines μ ν U hU,
        ih]

theorem coordinate_recovery_moments
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν)
    (hU : CoordinateMultiplicationIntertwines μ ν U)
    (hone : U (coordinateConstantOne μ) = coordinateConstantOne ν) (a : ℝ) (n : ℕ) :
    (∫ t : ℝ, coordinateRecoveryKernel a t ^ n ∂μ) =
      ∫ t : ℝ, coordinateRecoveryKernel a t ^ n ∂ν := by
  apply Complex.ofReal_injective
  rw [← coordinate_recovery_power_inner, ← coordinate_recovery_power_inner]
  have he := U.inner_map_map (coordinateConstantOne μ) (coordinateRecoveryPower μ a n)
  rw [hone, coordinate_recovery_power_intertwines μ ν U hU hone] at he
  exact he.symm

def coordinateRecoveryCompact (a t : ℝ) : OpUnitInterval :=
  ⟨coordinateRecoveryKernel a t, (coordinate_recovery_kernel_pos a t).le,
    coordinate_recovery_kernel_le_one a t⟩

theorem coordinate_recovery_compact_measurable (a : ℝ) :
    Measurable (coordinateRecoveryCompact a) := by
  apply Measurable.subtype_mk
  unfold coordinateRecoveryKernel
  fun_prop

/-- These bounded probes determine finite measures on the entire real line;
no support or unbounded-moment hypothesis is needed. -/
theorem coordinate_recovery_measures_unique (ρ σ : Measure ℝ)
    [IsFiniteMeasure ρ] [IsFiniteMeasure σ]
    (hm : ∀ a : ℝ, ∀ n : ℕ,
      (∫ t : ℝ, coordinateRecoveryKernel a t ^ n ∂ρ) =
        ∫ t : ℝ, coordinateRecoveryKernel a t ^ n ∂σ) : ρ = σ := by
  have he (a : ℝ) : ρ.map (coordinateRecoveryCompact a) =
      σ.map (coordinateRecoveryCompact a) := by
    apply operator_hausdorff_moment_unique
    intro n
    rw [integral_map (coordinate_recovery_compact_measurable a).aemeasurable
        ((continuous_subtype_val.pow n).aestronglyMeasurable),
      integral_map (coordinate_recovery_compact_measurable a).aemeasurable
        ((continuous_subtype_val.pow n).aestronglyMeasurable)]
    exact hm a n
  have hcc (x y : ℝ) (hxy : x ≤ y) : ρ (Icc x y) = σ (Icc x y) := by
    let a := (x+y)/2
    let d := (y-x)/2
    let E : Set OpUnitInterval := {q | (1+d^2)⁻¹ ≤ (q : ℝ)}
    have hE : MeasurableSet E := measurableSet_le measurable_const measurable_subtype_coe
    have hpre : coordinateRecoveryCompact a ⁻¹' E = Icc x y := by
      ext t
      change (1+d^2)⁻¹ ≤ (1+(t-a)^2)⁻¹ ↔ x ≤ t ∧ t ≤ y
      rw [inv_le_inv₀ (by positivity) (by positivity)]
      dsimp [a, d]
      constructor
      · intro h
        constructor <;> nlinarith [sq_nonneg (t-(x+y)/2)]
      · rintro ⟨hxt, hty⟩
        nlinarith [mul_nonneg (sub_nonneg.mpr hxt) (sub_nonneg.mpr hty)]
    have h := congrArg (fun M : Measure OpUnitInterval => M E) (he a)
    simpa only [Measure.map_apply (coordinate_recovery_compact_measurable a) hE,
      hpre] using h
  apply Measure.ext_of_Ioc
  intro x y hxy
  have hset : Ioc x y = Icc x y \ {x} := by
    ext t
    simp only [mem_Ioc, mem_diff, mem_Icc, mem_singleton_iff]
    constructor
    · rintro ⟨hx, hy⟩
      exact ⟨⟨hx.le, hy⟩, ne_of_gt hx⟩
    · rintro ⟨⟨hx, hy⟩, hn⟩
      exact ⟨lt_of_le_of_ne hx (Ne.symm hn), hy⟩
  rw [hset, measure_diff (by simpa using hxy.le) (measurableSet_singleton x).nullMeasurableSet
      (measure_ne_top ρ {x}),
    measure_diff (by simpa using hxy.le) (measurableSet_singleton x).nullMeasurableSet
      (measure_ne_top σ {x}), hcc x y hxy.le]
  have hs := hcc x x le_rfl
  simpa only [Icc_self] using congrArg (fun z => σ (Icc x y) - z) hs

/-- The fully marked unbounded multiplication operator and its constant
vector identify the actual coordinate probability, on the full real line. -/
theorem marked_multiplication_unitary_preserves_probability
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν)
    (hU : CoordinateMultiplicationIntertwines μ ν U)
    (hone : U (coordinateConstantOne μ) = coordinateConstantOne ν) : μ = ν :=
  coordinate_recovery_measures_unique μ ν (coordinate_recovery_moments μ ν U hU hone)

end
end Sigma
