import SigmaProbGammaBetaChange

namespace Sigma
noncomputable section
open MeasureTheory Measure Set Filter ProbabilityTheory
open scoped ENNReal

def gammaBetaGammaReal (a x : ℝ) : ℝ :=
  1 / Real.Gamma a * x^(a-1) * Real.exp (-x)

def gammaBetaReal (a b : ℝ) : ℝ :=
  Real.Gamma (2*a) / (Real.Gamma a)^2 * b^(a-1) * (1-b)^(a-1)

def gammaBetaGammaFactor (a x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (gammaBetaGammaReal a x)

def gammaBetaFactor (a b : ℝ) : ℝ≥0∞ := ENNReal.ofReal (gammaBetaReal a b)

def gammaBetaMeasure (a : ℝ) : Measure ℝ :=
  (volume.restrict (Ioo 0 1)).withDensity (gammaBetaFactor a)

theorem gamma_beta_gamma_real_measurable (a : ℝ) : Measurable (gammaBetaGammaReal a) := by
  unfold gammaBetaGammaReal
  fun_prop

theorem gamma_beta_real_measurable (a : ℝ) : Measurable (gammaBetaReal a) := by
  unfold gammaBetaReal
  fun_prop

theorem gamma_beta_gamma_factor_measurable (a : ℝ) : Measurable (gammaBetaGammaFactor a) :=
  (gamma_beta_gamma_real_measurable a).ennreal_ofReal

theorem gamma_beta_factor_measurable (a : ℝ) : Measurable (gammaBetaFactor a) :=
  (gamma_beta_real_measurable a).ennreal_ofReal

theorem gamma_beta_gamma_real_pos (a x : ℝ) (ha : 0 < a) (hx : 0 < x) :
    0 < gammaBetaGammaReal a x := by
  unfold gammaBetaGammaReal
  positivity

theorem gamma_beta_real_pos (a b : ℝ) (ha : 0 < a) (hb : b ∈ Ioo (0 : ℝ) 1) :
    0 < gammaBetaReal a b := by
  have hb0 : 0 < b := hb.1
  have hb1 : 0 < 1-b := sub_pos.mpr hb.2
  unfold gammaBetaReal
  positivity

theorem gamma_beta_gamma_measure (a : ℝ) :
    gammaMeasure a 1 = (volume.restrict (Ioi 0)).withDensity (gammaBetaGammaFactor a) := by
  rw [← withDensity_indicator measurableSet_Ioi]
  apply withDensity_congr_ae
  have hzero : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    apply ae_iff.mpr
    simp
  filter_upwards [hzero] with x hx
  by_cases hp : 0 < x
  · rw [Set.indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hp)]
    simp [gammaPDF, gammaPDFReal, hp.le, gammaBetaGammaFactor, gammaBetaGammaReal]
  · have hn : x < 0 := lt_of_le_of_ne (le_of_not_gt hp) hx
    rw [Set.indicator_of_not_mem (show x ∉ Ioi (0 : ℝ) from hp), gammaPDF_of_neg hn]

theorem gamma_beta_density_real_identity (a t b : ℝ) (ha : 0 < a)
    (ht : 0 < t) (hb : b ∈ Ioo (0 : ℝ) 1) :
    gammaBetaGammaReal (2*a) t * gammaBetaReal a b =
      t * (gammaBetaGammaReal a (t*b) * gammaBetaGammaReal a (t*(1-b))) := by
  have hb0 : 0 < b := hb.1
  have hb1 : 0 < 1-b := sub_pos.mpr hb.2
  have hg : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hgg : Real.Gamma (2*a) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hp : t^(2*a-1) = t*(t^(a-1)*t^(a-1)) := by
    calc
      t^(2*a-1) = t^(1+((a-1)+(a-1))) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add ht, Real.rpow_one, Real.rpow_add ht]
  have he : Real.exp (-(t*b)) * Real.exp (-(t*(1-b))) = Real.exp (-t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold gammaBetaGammaReal gammaBetaReal
  rw [Real.mul_rpow ht.le hb0.le, Real.mul_rpow ht.le hb1.le, hp]
  calc
    _ = t * (1 / Real.Gamma a * (t^(a-1)*b^(a-1)) *
      (1 / Real.Gamma a * (t^(a-1)*(1-b)^(a-1)))) * Real.exp (-t) := by
        field_simp
        ring
    _ = _ := by rw [← he]; ring

theorem gamma_beta_density_identity (a : ℝ) (ha : 0 < a)
    (p : ℝ × ℝ) (hp : p ∈ gammaBetaSplitDomain) :
    gammaBetaGammaFactor (2*a) p.1 * gammaBetaFactor a p.2 =
      ENNReal.ofReal p.1 * (gammaBetaGammaFactor a (gammaBetaSplit p).1 *
        gammaBetaGammaFactor a (gammaBetaSplit p).2) := by
  have ht : 0 < p.1 := hp.1
  have hb : p.2 ∈ Ioo (0 : ℝ) 1 := hp.2
  unfold gammaBetaGammaFactor gammaBetaFactor
  simp only [gammaBetaSplit]
  rw [← ENNReal.ofReal_mul (gamma_beta_gamma_real_pos _ _ (by positivity) ht).le,
    ← ENNReal.ofReal_mul (gamma_beta_gamma_real_pos _ _ ha (mul_pos ht hb.1)).le,
    ← ENNReal.ofReal_mul ht.le]
  exact congrArg ENNReal.ofReal (gamma_beta_density_real_identity a p.1 p.2 ha ht hb)

theorem gamma_beta_split_measure (a : ℝ) (ha : 0 < a) :
    ((gammaMeasure (2*a) 1).prod (gammaBetaMeasure a)).map gammaBetaSplit =
      (gammaMeasure a 1).prod (gammaMeasure a 1) := by
  have hsrc := gamma_beta_product_withDensity (volume.restrict (Ioi (0 : ℝ)))
    (volume.restrict (Ioo (0 : ℝ) 1)) (gammaBetaGammaFactor (2*a)) (gammaBetaFactor a)
    (gamma_beta_gamma_factor_measurable (2*a)) (gamma_beta_factor_measurable a)
    (fun _ => ENNReal.ofReal_ne_top) (fun _ => ENNReal.ofReal_ne_top)
  have htgt := gamma_beta_product_withDensity (volume.restrict (Ioi (0 : ℝ)))
    (volume.restrict (Ioi (0 : ℝ))) (gammaBetaGammaFactor a) (gammaBetaGammaFactor a)
    (gamma_beta_gamma_factor_measurable a) (gamma_beta_gamma_factor_measurable a)
    (fun _ => ENNReal.ofReal_ne_top) (fun _ => ENNReal.ofReal_ne_top)
  rewrite [gamma_beta_gamma_measure (2*a), gammaBetaMeasure, hsrc, prod_restrict]
  rewrite [gamma_beta_gamma_measure a, htgt, prod_restrict]
  have hρ : Measurable (fun p : ℝ × ℝ =>
      gammaBetaGammaFactor a p.1 * gammaBetaGammaFactor a p.2) :=
    ((gamma_beta_gamma_factor_measurable a).comp measurable_fst).mul
      ((gamma_beta_gamma_factor_measurable a).comp measurable_snd)
  have he : ((volume : Measure (ℝ × ℝ)).restrict gammaBetaSplitDomain).withDensity
      (fun p => gammaBetaGammaFactor (2*a) p.1 * gammaBetaFactor a p.2) =
      ((volume : Measure (ℝ × ℝ)).restrict gammaBetaSplitDomain).withDensity
        (fun p => ENNReal.ofReal p.1 *
          (gammaBetaGammaFactor a (gammaBetaSplit p).1 * gammaBetaGammaFactor a (gammaBetaSplit p).2)) := by
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)] with p hp
    exact gamma_beta_density_identity a ha p hp
  have hmap := gamma_beta_split_density_map
    (fun p => gammaBetaGammaFactor a p.1 * gammaBetaGammaFactor a p.2) hρ
  rewrite [← he] at hmap
  simpa only [gammaBetaSplitDomain] using hmap

end
end Sigma
