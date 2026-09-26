import SigmaProbCompletion
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace Sigma
noncomputable section
open MeasureTheory Measure Set Filter
open scoped ENNReal

def gammaBetaSplit (p : ℝ × ℝ) : ℝ × ℝ := (p.1*p.2, p.1*(1-p.2))

def gammaBetaSplitDomain : Set (ℝ × ℝ) := Ioi 0 ×ˢ Ioo 0 1

def gammaBetaSplitDerivative (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin (Basis.finTwoProd ℝ) (Basis.finTwoProd ℝ)
    !![p.2, p.1; 1-p.2, -p.1])

theorem gamma_beta_split_measurable : Measurable gammaBetaSplit := by
  unfold gammaBetaSplit
  fun_prop

theorem gamma_beta_split_derivative (p : ℝ × ℝ) :
    HasFDerivAt gammaBetaSplit (gammaBetaSplitDerivative p) p := by
  rw [gammaBetaSplitDerivative, Matrix.toLin_finTwoProd_toContinuousLinearMap]
  convert HasFDerivAt.prod (𝕜 := ℝ)
    (hasFDerivAt_fst.mul hasFDerivAt_snd)
    (hasFDerivAt_fst.mul ((hasFDerivAt_const (1 : ℝ) p).sub hasFDerivAt_snd)) using 2
  all_goals simp [gammaBetaSplit, smul_smul, add_comm, neg_smul]
  all_goals module

theorem gamma_beta_split_det (p : ℝ × ℝ) : (gammaBetaSplitDerivative p).det = -p.1 := by
  simp only [gammaBetaSplitDerivative, LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of]
  ring

theorem gamma_beta_split_injective : InjOn gammaBetaSplit gammaBetaSplitDomain := by
  intro p hp q hq he
  have he1 := congrArg Prod.fst he
  have he2 := congrArg Prod.snd he
  dsimp [gammaBetaSplit] at he1 he2
  have ht : p.1 = q.1 := by nlinarith
  apply Prod.ext ht
  rw [ht] at he1
  exact mul_left_cancel₀ (ne_of_gt hq.1) he1

theorem gamma_beta_split_image :
    gammaBetaSplit '' gammaBetaSplitDomain = Ioi 0 ×ˢ Ioi 0 := by
  ext p
  constructor
  · rintro ⟨⟨t,b⟩,⟨ht,hb⟩,rfl⟩
    exact ⟨mul_pos ht hb.1, mul_pos ht (sub_pos.mpr hb.2)⟩
  · rintro ⟨hx,hy⟩
    change 0 < p.1 at hx
    change 0 < p.2 at hy
    have ht : 0 < p.1+p.2 := add_pos hx hy
    refine ⟨(p.1+p.2, p.1/(p.1+p.2)),⟨ht,div_pos hx ht,(div_lt_one ht).mpr ?_⟩,?_⟩
    · linarith
    · apply Prod.ext <;> dsimp [gammaBetaSplit] <;> field_simp [ht.ne']

/-- The literal two-dimensional change of variables underlying Gamma–Beta
splitting. It is valid for every nonnegative integrand. -/
theorem gamma_beta_split_lintegral (f : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ p in Ioi 0 ×ˢ Ioi 0, f p) =
      ∫⁻ p in gammaBetaSplitDomain, ENNReal.ofReal p.1 * f (gammaBetaSplit p) := by
  letI : IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul (volume : Measure (ℝ × ℝ))
    (measurableSet_Ioi.prod measurableSet_Ioo)
    (fun p (_ : p ∈ gammaBetaSplitDomain) => (gamma_beta_split_derivative p).hasFDerivWithinAt)
    gamma_beta_split_injective f
  change (∫⁻ p in gammaBetaSplit '' gammaBetaSplitDomain, f p) = _ at h
  rw [gamma_beta_split_image] at h
  rw [h]
  apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
  exact Eventually.of_forall fun p hp => by
    rw [gamma_beta_split_det, abs_neg, abs_of_pos hp.1]

theorem gamma_beta_product_withDensity (μ ν : Measure ℝ) [SigmaFinite μ] [SigmaFinite ν]
    (f g : ℝ → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (hfnt : ∀ x, f x ≠ ∞) (hgnt : ∀ x, g x ≠ ∞) :
    (μ.withDensity f).prod (ν.withDensity g) =
      (μ.prod ν).withDensity (fun p => f p.1 * g p.2) := by
  letI := SigmaFinite.withDensity_of_ne_top' (μ := μ) hfnt
  letI := SigmaFinite.withDensity_of_ne_top' (μ := ν) hgnt
  apply Measure.prod_eq
  intro s t hs ht
  rw [withDensity_apply _ (hs.prod ht), ← prod_restrict,
    lintegral_prod_mul hf.aemeasurable hg.aemeasurable,
    withDensity_apply _ hs, withDensity_apply _ ht]

theorem gamma_beta_split_density_map (ρ : ℝ × ℝ → ℝ≥0∞) (hρ : Measurable ρ) :
    (((volume : Measure (ℝ × ℝ)).restrict gammaBetaSplitDomain).withDensity
      (fun p => ENNReal.ofReal p.1 * ρ (gammaBetaSplit p))).map gammaBetaSplit =
      ((volume : Measure (ℝ × ℝ)).restrict (Ioi 0 ×ˢ Ioi 0)).withDensity ρ := by
  have hsrc : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * ρ (gammaBetaSplit p)) :=
    measurable_fst.ennreal_ofReal.mul (hρ.comp gamma_beta_split_measurable)
  have hI (g : ℝ × ℝ → ℝ≥0∞) (hg : Measurable g) :
      (∫⁻ p, g p ∂(((volume : Measure (ℝ × ℝ)).restrict gammaBetaSplitDomain).withDensity
        (fun p => ENNReal.ofReal p.1 * ρ (gammaBetaSplit p))).map gammaBetaSplit) =
      ∫⁻ p, g p ∂((volume : Measure (ℝ × ℝ)).restrict (Ioi 0 ×ˢ Ioi 0)).withDensity ρ := by
    rw [lintegral_map hg gamma_beta_split_measurable,
      lintegral_withDensity_eq_lintegral_mul _ hsrc
        (show Measurable (fun p => g (gammaBetaSplit p)) from hg.comp gamma_beta_split_measurable),
      lintegral_withDensity_eq_lintegral_mul _ hρ hg]
    simp only [Pi.mul_apply]
    rw [gamma_beta_split_lintegral]
    exact lintegral_congr fun p => mul_assoc _ _ _
  ext s hs
  have h := hI (s.indicator (fun _ => 1)) (measurable_const.indicator hs)
  simpa only [lintegral_indicator_const hs, one_mul] using h

end
end Sigma
