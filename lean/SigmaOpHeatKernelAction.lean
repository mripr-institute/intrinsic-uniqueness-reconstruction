import SigmaOpHeatKernelRowFourier

namespace Sigma
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal
set_option maxHeartbeats 6000000

/-- The Fourier--Laguerre formula for evaluating the heat action at a positive point. -/
def laguerreHeatActionTerm (τ x : ℝ) (f : LaguerreWeightedHilbert) (n : ℕ) : ℂ :=
  (((Real.exp (-τ))^n * opLaguerre n x / Real.sqrt (n+1) : ℝ) : ℂ) *
    laguerreHilbertBasis.repr f n

theorem laguerre_heat_action_summable {τ x : ℝ} (hτ : 0 < τ) (hx : 0 < x)
    (f : LaguerreWeightedHilbert) : Summable (laguerreHeatActionTerm τ x f) := by
  let r := Real.exp (-τ)
  let t := (1-r)/2
  let q := 1+t
  let ρ := r*q
  let C := q/t * Real.exp (x/t)
  have hr : 0 < r ∧ r < 1 := by
    constructor
    · exact Real.exp_pos _
    · dsimp [r]
      rw [Real.exp_lt_one_iff]
      linarith
  have ht : 0 < t := by dsimp [t]; linarith
  have hq : 0 < q := by dsimp [q]; linarith
  have hρ : 0 ≤ ρ ∧ ρ < 1 := by
    constructor
    · dsimp [ρ]; positivity
    · dsimp [ρ, q, t]
      nlinarith [sq_nonneg (r-1)]
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hL (n : ℕ) : |opLaguerre n x| ≤ C*q^n := by
    have h := op_laguerre_geometric_bound ht hx.le hx.le le_rfl n
    calc
      |opLaguerre n x| ≤ q^(n+1)/t * Real.exp (x/t) := by simpa [q] using h
      _ = C*q^n := by dsimp [C]; rw [pow_succ]; ring
  have hsum : Summable (fun n : ℕ => (C*‖f‖)*ρ^n) :=
    (summable_geometric_of_lt_one hρ.1 hρ.2).mul_left _
  apply Summable.of_norm_bounded _ hsum
  intro n
  have hcoord : ‖laguerreHilbertBasis.repr f n‖ ≤ ‖f‖ := by
    exact (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (laguerreHilbertBasis.repr f) n).trans_eq
      (laguerreHilbertBasis.repr.norm_map f)
  have hroot : 1 ≤ Real.sqrt (n+1:ℝ) := Real.one_le_sqrt.mpr (by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
  have hcoef : |r^n * opLaguerre n x / Real.sqrt (n+1:ℝ)| ≤ r^n*|opLaguerre n x| := by
    rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _), abs_mul,
      abs_of_nonneg (pow_nonneg hr.1.le n)]
    exact (div_le_iff₀ (by positivity)).2 (by
      nlinarith [mul_nonneg (pow_nonneg hr.1.le n) (abs_nonneg (opLaguerre n x))])
  change ‖(((r^n * opLaguerre n x / Real.sqrt (n+1) : ℝ) : ℂ) *
    laguerreHilbertBasis.repr f n)‖ ≤ (C*‖f‖)*ρ^n
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    |r^n * opLaguerre n x / Real.sqrt (n+1:ℝ)| *
        ‖laguerreHilbertBasis.repr f n‖ ≤
        (r^n*|opLaguerre n x|)*‖f‖ :=
      mul_le_mul hcoef hcoord (norm_nonneg _) (by positivity)
    _ ≤ (r^n*(C*q^n))*‖f‖ := by
      gcongr
      exact hL n
    _ = (C*‖f‖)*ρ^n := by dsimp [ρ]; rw [mul_pow]; ring

private theorem laguerre_heat_basis_term_coe_ae {τ : ℝ} (hτ : 0 < τ)
    (f : LaguerreWeightedHilbert) (n : ℕ) :
    ((laguerreHilbertBasis.repr (laguerreHeatOperator τ hτ.le f) n •
      laguerreHilbertBasis n : LaguerreWeightedHilbert) : ℝ → ℂ) =ᵐ[
      gammaProbability] fun x => laguerreHeatActionTerm τ x f n := by
  have hs₁ := Lp.coeFn_smul
    (laguerreHilbertBasis.repr (laguerreHeatOperator τ hτ.le f) n)
    (laguerreHilbertBasis n)
  have hs₂ := Lp.coeFn_smul ((Real.sqrt (n+1) : ℂ)⁻¹)
    (laguerreL2Vector n)
  have hb : (laguerreHilbertBasis n : ℝ → ℂ) =ᵐ[gammaProbability]
      fun x => ((Real.sqrt (n+1) : ℂ)⁻¹) * (opLaguerre n x : ℂ) := by
    rw [laguerre_hilbert_basis_apply, normalizedLaguerreL2Vector]
    filter_upwards [hs₂, (op_laguerre_complex_mem_l2 n).coeFn_toLp] with x h₁ h₂
    change laguerreL2Vector n x = _ at h₂
    rw [h₁, Pi.smul_apply, smul_eq_mul, h₂]
  filter_upwards [hs₁, hb] with x h₁ h₂
  rw [h₁, Pi.smul_apply, smul_eq_mul, h₂, laguerre_heat_coordinate]
  have he : Real.exp (-τ*(n:ℝ)) = Real.exp (-τ)^n := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he]
  simp only [laguerreHeatActionTerm]
  push_cast
  ring

private theorem laguerre_heat_basis_partial_coe_ae {τ : ℝ} (hτ : 0 < τ)
    (f : LaguerreWeightedHilbert) (N : ℕ) :
    ((∑ n ∈ Finset.range N,
      laguerreHilbertBasis.repr (laguerreHeatOperator τ hτ.le f) n •
        laguerreHilbertBasis n : LaguerreWeightedHilbert) : ℝ → ℂ) =ᵐ[
      gammaProbability] fun x => ∑ n ∈ Finset.range N,
        laguerreHeatActionTerm τ x f n := by
  induction N with
  | zero =>
      simp only [Finset.sum_range_zero]
      exact Filter.Eventually.of_forall (fun x => by simp)
  | succ N ih =>
      simp only [Finset.sum_range_succ]
      have hadd := Lp.coeFn_add
        (∑ n ∈ Finset.range N,
          laguerreHilbertBasis.repr (laguerreHeatOperator τ hτ.le f) n •
            laguerreHilbertBasis n)
        (laguerreHilbertBasis.repr (laguerreHeatOperator τ hτ.le f) N •
          laguerreHilbertBasis N)
      filter_upwards [hadd, ih, laguerre_heat_basis_term_coe_ae hτ f N]
        with x h₁ h₂ h₃
      rw [h₁, Pi.add_apply, h₂, h₃]

/-- The native heat operator has the pointwise spectral series as its
Gamma-almost-everywhere representative for every Hilbert-space input. -/
theorem laguerre_heat_action_series_represents {τ : ℝ} (hτ : 0 < τ)
    (f : LaguerreWeightedHilbert) :
    ((laguerreHeatOperator τ hτ.le f : LaguerreWeightedHilbert) : ℝ → ℂ) =ᵐ[
      gammaProbability] fun x => ∑' n : ℕ, laguerreHeatActionTerm τ x f n := by
  let S : ℕ → LaguerreWeightedHilbert := fun N =>
    ∑ n ∈ Finset.range N,
      laguerreHilbertBasis.repr (laguerreHeatOperator τ hτ.le f) n •
        laguerreHilbertBasis n
  let g : ℕ → ℝ → ℂ := fun N x =>
    ∑ n ∈ Finset.range N, laguerreHeatActionTerm τ x f n
  let h : ℝ → ℂ := fun x => ∑' n : ℕ, laguerreHeatActionTerm τ x f n
  have hS : Tendsto S atTop (𝓝 (laguerreHeatOperator τ hτ.le f)) :=
    (laguerreHilbertBasis.hasSum_repr (laguerreHeatOperator τ hτ.le f)).tendsto_sum_nat
  have hmeasure := tendstoInMeasure_of_tendsto_Lp hS
  obtain ⟨ns, hns, hae⟩ := hmeasure.exists_seq_tendsto_ae
  have hrep : ∀ᵐ x : ℝ ∂gammaProbability, ∀ N : ℕ, S N x = g N x := by
    rw [ae_all_iff]
    intro N
    exact laguerre_heat_basis_partial_coe_ae hτ f N
  have hpos : ∀ᵐ x : ℝ ∂gammaProbability, 0 < x := by
    have hn : ∀ᵐ x : ℝ ∂gammaProbability, 0 ≤ x := by
      simpa only [ae_iff, not_le] using gamma_probability_negative_ray
    have hne : ∀ᵐ x : ℝ ∂gammaProbability, x ≠ 0 := by
      rw [ae_iff]
      simpa only [not_ne_iff, Set.setOf_eq_eq_singleton] using
        gamma_probability_no_atom 0
    filter_upwards [hn, hne] with x hx hxn
    exact lt_of_le_of_ne hx (Ne.symm hxn)
  filter_upwards [hae, hrep, hpos] with x hx hrep hxpos
  have hpoint : Tendsto (fun N => g N x) atTop (𝓝 (h x)) :=
    (laguerre_heat_action_summable hτ hxpos f).hasSum.tendsto_sum_nat
  have hpoint' : Tendsto (fun i => g (ns i) x) atTop (𝓝 (h x)) :=
    hpoint.comp hns.tendsto_atTop
  have hrewrite : (fun i => S (ns i) x) = fun i => g (ns i) x := by
    funext i
    exact hrep (ns i)
  rw [hrewrite] at hx
  exact tendsto_nhds_unique hx hpoint'

/-- Integrating a row of the closed kernel against an arbitrary Hilbert-space
input is the Hilbert inner product with that actual L² row. -/
theorem laguerre_heat_kernel_row_inner_integral {τ x : ℝ} (hτ : 0 < τ)
    (hx : 0 < x) (f : LaguerreWeightedHilbert) :
    @inner ℂ LaguerreWeightedHilbert _ (laguerreHeatKernelRow τ x hτ hx) f =
      ∫ y : ℝ, (laguerreHeatKernel τ x y : ℂ) * f y ∂gammaProbability := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [laguerre_heat_kernel_row_coe_ae hτ hx] with y hy
  rw [hy]
  simp [RCLike.inner_apply]

private theorem laguerre_row_inner_eq_action_of_coordinate {τ x : ℝ}
    (row : LaguerreWeightedHilbert)
    (hcoord : ∀ n : ℕ, laguerreHilbertBasis.repr row n =
      (((Real.exp (-τ))^n * opLaguerre n x / Real.sqrt (n+1) : ℝ) : ℂ))
    (f : LaguerreWeightedHilbert) :
    @inner ℂ LaguerreWeightedHilbert _ row f =
      ∑' n : ℕ, laguerreHeatActionTerm τ x f n := by
  rw [← laguerreHilbertBasis.repr.inner_map_map, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  rw [hcoord n]
  simp only [RCLike.inner_apply, laguerreHeatActionTerm, Complex.star_def,
    Complex.conj_ofReal]

/-- The closed kernel's density with respect to Lebesgue measure is exactly
its Gamma-relative kernel multiplied by the paper's Gamma density. -/
theorem laguerre_heat_kernel_lebesgue_integral (τ x : ℝ) (f : ℝ → ℝ) :
    (∫ y : ℝ, laguerreHeatKernel τ x y * f y ∂gammaProbability) =
      ∫ y : ℝ in Set.Ioi 0,
        (laguerreHeatKernel τ x y * SigmaPresentations.density y) * f y := by
  rw [gamma_probability_integral]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  ring

/-- The Hille--Hardy formula is the integral kernel of the actual native heat
operator on every vector of the Gamma-weighted Hilbert space. -/
theorem laguerre_heat_kernel_integral_eq_operator {τ : ℝ} (hτ : 0 < τ)
    (f : LaguerreWeightedHilbert) :
    (fun x : ℝ => ∫ y : ℝ,
      (laguerreHeatKernel τ x y : ℂ) * f y ∂gammaProbability) =ᵐ[
        gammaProbability]
      fun x => (laguerreHeatOperator τ hτ.le f : ℝ → ℂ) x := by
  have hp : ∀ᵐ x : ℝ ∂gammaProbability, 0 < x := by
    have hn : ∀ᵐ x : ℝ ∂gammaProbability, 0 ≤ x := by
      simpa only [ae_iff, not_le] using gamma_probability_negative_ray
    have hne : ∀ᵐ x : ℝ ∂gammaProbability, x ≠ 0 := by
      rw [ae_iff]
      simpa only [not_ne_iff, Set.setOf_eq_eq_singleton] using
        gamma_probability_no_atom 0
    filter_upwards [hn, hne] with x hx hxn
    exact lt_of_le_of_ne hx (Ne.symm hxn)
  filter_upwards [hp, (laguerre_heat_action_series_represents hτ f).symm]
    with x hx hrep
  calc
    (∫ y : ℝ, (laguerreHeatKernel τ x y : ℂ) * f y ∂gammaProbability) =
        @inner ℂ LaguerreWeightedHilbert _ (laguerreHeatKernelRow τ x hτ hx) f :=
      (laguerre_heat_kernel_row_inner_integral hτ hx f).symm
    _ = ∑' n : ℕ, laguerreHeatActionTerm τ x f n :=
      laguerre_row_inner_eq_action_of_coordinate _
        (laguerre_heat_kernel_row_coordinate hτ hx) f
    _ = (laguerreHeatOperator τ hτ.le f : ℝ → ℂ) x := hrep

end
end Sigma
