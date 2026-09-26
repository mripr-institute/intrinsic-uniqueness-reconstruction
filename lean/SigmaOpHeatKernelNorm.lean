import SigmaOpHeatKernelPointwise
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! The exact weighted product-L² norm used in the proof of
paper `final:O4-resolvents`. -/

namespace Sigma
noncomputable section
open MeasureTheory Filter
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace

theorem laguerre_heat_kernel_spectral_term_coe (r : ℝ) (n : ℕ) :
    (laguerreHeatKernelSpectralTerm r n : ℝ × ℝ → ℝ) =ᵐ[
      gammaProbability.prod gammaProbability]
      fun z => (r^n/(n+1:ℝ))*opLaguerre n z.1*opLaguerre n z.2 :=
  Memℒp.coeFn_toLp _

theorem laguerre_heat_kernel_spectral_term_inner (r s : ℝ) (n m : ℕ) :
    @inner ℝ LaguerreProductHilbert _
      (laguerreHeatKernelSpectralTerm r n) (laguerreHeatKernelSpectralTerm s m) =
        if n = m then r^n*s^n else 0 := by
  rw [L2.inner_def]
  calc
    _ = ∫ z : ℝ × ℝ,
        ((r^n/(n+1:ℝ))*(s^m/(m+1:ℝ))) *
          ((opLaguerre n z.1*opLaguerre m z.1)*
            (opLaguerre n z.2*opLaguerre m z.2))
        ∂gammaProbability.prod gammaProbability := by
      apply integral_congr_ae
      filter_upwards [laguerre_heat_kernel_spectral_term_coe r n,
        laguerre_heat_kernel_spectral_term_coe s m] with z hn hm
      rw [hn, hm]
      simp only [RCLike.inner_apply, conj_trivial]
      ring
    _ = _ := by
      rw [integral_mul_left,
        integral_prod_mul (fun x => opLaguerre n x*opLaguerre m x)
          (fun y => opLaguerre n y*opLaguerre m y), op_laguerre_pair_integral]
      split_ifs with h
      · subst m
        have hn : (n+1:ℝ) ≠ 0 := by positivity
        field_simp
      · simp

theorem laguerre_heat_kernel_spectral_series_inner {r s : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (hs : 0 ≤ s) (hs1 : s < 1) :
    @inner ℝ LaguerreProductHilbert _
      (laguerreHeatKernelSpectralSeries r) (laguerreHeatKernelSpectralSeries s) =
        (1-r*s)⁻¹ := by
  have hsr := laguerre_heat_kernel_spectral_series_summable hr hr1
  have hss := laguerre_heat_kernel_spectral_series_summable hs hs1
  have hi (n : ℕ) : @inner ℝ LaguerreProductHilbert _
      (laguerreHeatKernelSpectralTerm r n) (laguerreHeatKernelSpectralSeries s) = r^n*s^n := by
    have he := (hss.hasSum.mapL (innerSL ℝ (laguerreHeatKernelSpectralTerm r n))).tsum_eq
    change (∑' m : ℕ, @inner ℝ LaguerreProductHilbert _
      (laguerreHeatKernelSpectralTerm r n) (laguerreHeatKernelSpectralTerm s m)) =
      @inner ℝ LaguerreProductHilbert _ (laguerreHeatKernelSpectralTerm r n)
        (laguerreHeatKernelSpectralSeries s) at he
    rw [← he]
    simp only [laguerre_heat_kernel_spectral_term_inner]
    rw [tsum_eq_single n]
    · simp
    · intro m hm
      simp [Ne.symm hm]
  have hsum := hsr.hasSum.mapL (innerSL ℝ (laguerreHeatKernelSpectralSeries s))
  have he : HasSum (fun n : ℕ => (r*s)^n)
      (@inner ℝ LaguerreProductHilbert _
        (laguerreHeatKernelSpectralSeries r) (laguerreHeatKernelSpectralSeries s)) := by
    convert hsum using 1
    · funext n
      change (r*s)^n = @inner ℝ LaguerreProductHilbert _
        (laguerreHeatKernelSpectralSeries s) (laguerreHeatKernelSpectralTerm r n)
      rw [real_inner_comm, hi, mul_pow]
    · exact real_inner_comm _ _
  have hrs : r*s < 1 := by nlinarith [mul_nonneg hr (sub_nonneg.mpr hs1.le)]
  exact he.unique (hasSum_geometric_of_lt_one (mul_nonneg hr hs) hrs)

/-- The sharp kernel norm: its square has a geometric singularity of order
one, so the norm itself has order one half at time zero. -/
theorem laguerre_heat_kernel_norm_sq {τ : ℝ} (hτ : 0 < τ) :
    ‖(laguerre_heat_kernel_mem_product_l2 hτ).toLp
      (fun z : ℝ × ℝ => laguerreHeatKernel τ z.1 z.2)‖^2 =
      (1-Real.exp (-2*τ))⁻¹ := by
  have hr : Real.exp (-τ) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  rw [laguerre_heat_kernel_product_l2_eq_spectral hτ, norm_sq_eq_inner (𝕜 := ℝ)]
  rw [laguerre_heat_kernel_spectral_series_inner (Real.exp_pos _).le hr
    (Real.exp_pos _).le hr]
  change (1-Real.exp (-τ)*Real.exp (-τ))⁻¹ = _
  rw [← Real.exp_add]
  congr 3
  ring

/-- The actual closed heat kernel as a vector at a positive time. -/
def laguerreHeatKernelVector (τ : Set.Ioi (0:ℝ)) : LaguerreProductHilbert :=
  laguerreHeatKernelSpectralSeries (Real.exp (-τ.val))

theorem laguerre_heat_kernel_vector_norm_sq (τ : Set.Ioi (0:ℝ)) :
    ‖laguerreHeatKernelVector τ‖^2 = (1-Real.exp (-2*τ.val))⁻¹ := by
  rw [← laguerre_heat_kernel_norm_sq τ.property,
    laguerre_heat_kernel_product_l2_eq_spectral τ.property]
  rfl

theorem laguerre_heat_kernel_term_smul (r : ℝ) (n : ℕ) :
    laguerreHeatKernelSpectralTerm r n = r^n • laguerreHeatKernelSpectralTerm 1 n := by
  apply Lp.ext
  filter_upwards [laguerre_heat_kernel_spectral_term_coe r n,
    laguerre_heat_kernel_spectral_term_coe 1 n,
    Lp.coeFn_smul (r^n) (laguerreHeatKernelSpectralTerm 1 n)] with z hr h1 hs
  rw [hr, hs, Pi.smul_apply, h1, smul_eq_mul]
  simp only [one_pow]
  ring

theorem laguerre_heat_kernel_vector_stronglyMeasurable :
    StronglyMeasurable laguerreHeatKernelVector := by
  let S : ℕ → Set.Ioi (0:ℝ) → LaguerreProductHilbert := fun N τ =>
    ∑ n ∈ Finset.range N, Real.exp (-τ.val)^n • laguerreHeatKernelSpectralTerm 1 n
  have hS (N : ℕ) : Continuous (S N) := by dsimp [S]; fun_prop
  apply stronglyMeasurable_of_tendsto atTop (fun N => (hS N).stronglyMeasurable)
  apply tendsto_pi_nhds.mpr
  intro τ
  have h := laguerre_heat_kernel_spectral_series_tendsto (Real.exp_pos (-τ.val)).le
    (Real.exp_lt_one_iff.mpr (neg_neg_of_pos τ.property))
  convert h using 1
  funext N
  apply Finset.sum_congr rfl
  intro n hn
  exact (laguerre_heat_kernel_term_smul _ n).symm

/-- A global bound with an integrable square-root singularity at zero. -/
theorem laguerre_heat_kernel_vector_norm_bound (τ : Set.Ioi (0:ℝ)) :
    ‖laguerreHeatKernelVector τ‖ ≤ 1+(Real.sqrt τ.val)⁻¹ := by
  have ht : 0 < τ.val := τ.property
  have he := Real.add_one_le_exp (2*τ.val)
  have hexp : 0 < Real.exp (2*τ.val)-1 := by
    have hh : 1 < Real.exp (2*τ.val) := Real.one_lt_exp_iff.mpr (by linarith)
    linarith
  have hrewrite : (1-Real.exp (-2*τ.val))⁻¹ =
      1+(Real.exp (2*τ.val)-1)⁻¹ := by
    rw [show -2*τ.val = -(2*τ.val) by ring, Real.exp_neg]
    field_simp [(Real.exp_ne_zero (2*τ.val)), hexp.ne']
  have hsquare : ‖laguerreHeatKernelVector τ‖^2 ≤ 1+(2*τ.val)⁻¹ := by
    rw [laguerre_heat_kernel_vector_norm_sq, hrewrite]
    exact add_le_add_left ((inv_le_inv₀ hexp (by positivity)).mpr (by linarith)) 1
  have hroot : 0 < Real.sqrt τ.val := Real.sqrt_pos.mpr ht
  have hroot2 := Real.sq_sqrt ht.le
  have hinv : (2*τ.val)⁻¹ ≤ (Real.sqrt τ.val)⁻¹^2 := by
    rw [inv_pow, hroot2]
    exact (inv_le_inv₀ (by positivity) ht).mpr (by linarith)
  have hnon : 0 ≤ (Real.sqrt τ.val)⁻¹ := (inv_pos.mpr hroot).le
  nlinarith [norm_nonneg (laguerreHeatKernelVector τ)]

private theorem positive_subtype_integrable {f : ℝ → ℝ}
    (hf : IntegrableOn f (Set.Ioi 0) volume) :
    Integrable (fun t : Set.Ioi (0:ℝ) => f t.val) := by
  have hm := hf.aestronglyMeasurable
  rw [IntegrableOn, ← map_comap_subtype_coe, integrable_map_measure] at hf
  · exact hf
  · simpa only [map_comap_subtype_coe measurableSet_Ioi] using hm
  · exact measurable_subtype_coe.aemeasurable
  · exact measurableSet_Ioi

/-- Both Laplace weights in O4-resolvents (k=0 and k=1) are integrable
against the actual kernel in weighted product L². -/
theorem laguerre_heat_kernel_weighted_integrable (a : ℝ) (ha : 0 < a) (k : ℕ) :
    Integrable (fun t : Set.Ioi (0:ℝ) =>
      (t.val^k * Real.exp (-a*t.val)) • laguerreHeatKernelVector t) := by
  have hk : (-1:ℝ) < (k:ℝ) := lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg k)
  have hk' : (-1:ℝ) < (k:ℝ)-(1/2:ℝ) := by
    have hkn := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hi := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) hk le_rfl ha
  have hi' := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) hk' le_rfl ha
  simp only [Real.rpow_one, Real.rpow_natCast] at hi hi'
  have hbound := positive_subtype_integrable (hi.add hi')
  have hweight : Continuous (fun t : Set.Ioi (0:ℝ) => t.val^k*Real.exp (-a*t.val)) := by
    fun_prop
  apply hbound.mono' (hweight.stronglyMeasurable.smul
    laguerre_heat_kernel_vector_stronglyMeasurable).aestronglyMeasurable
  apply Eventually.of_forall
  intro t
  have ht : 0 < t.val := t.property
  have hw : 0 ≤ t.val^k*Real.exp (-a*t.val) := by positivity
  rw [norm_smul, Real.norm_of_nonneg hw]
  calc
    _ ≤ (t.val^k*Real.exp (-a*t.val)) * (1+(Real.sqrt t.val)⁻¹) :=
      mul_le_mul_of_nonneg_left (laguerre_heat_kernel_vector_norm_bound t) hw
    _ = t.val^k*Real.exp (-a*t.val) +
        t.val^((k:ℝ)-(1/2:ℝ))*Real.exp (-a*t.val) := by
      rw [Real.rpow_sub ht, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
      ring

end
end Sigma
