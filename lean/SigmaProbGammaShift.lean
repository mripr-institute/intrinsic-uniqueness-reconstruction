import SigmaProbSurvivalBoundaries

namespace Sigma
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology ENNReal

/-- The shift restriction follows on the open positive ray; no endpoint derivative
or asymptotic hypothesis is needed. -/
theorem gamma_shift_ode_classification (f S : ℝ → ℝ) (k b c : ℝ) (hc : 0 < c)
    (hp : ∀ x > 0, 0 < f x)
    (hf : ∀ x > 0, HasDerivAt f ((k/x-b)*f x) x)
    (hS : ∀ x > 0, HasDerivAt S (-f x) x)
    (he : ∀ x > 0, S x = f (x+c)/f c) :
    k = 0 ∨ k = 1 ∧ c*b = 1 := by
  let R : ℝ → ℝ := fun x => f (x+c)/f c
  let A : ℝ → ℝ := fun x => b-k/(x+c)
  have hR (x : ℝ) (hx : 0 < x) :
      HasDerivAt R ((k/(x+c)-b)*R x) x := by
    convert ((hf (x+c) (by linarith)).comp x ((hasDerivAt_id x).add_const c)).div_const (f c) using 1
    dsimp [R]
    ring
  have hA (x : ℝ) (hx : 0 < x) : HasDerivAt A (k/(x+c)^2) x := by
    convert (((hasDerivAt_const x k).div ((hasDerivAt_id x).add_const c)
      (by dsimp; linarith : id x+c ≠ 0)).const_sub b) using 1
    simp only [A, id_eq, zero_mul, sub_zero, zero_sub, mul_one, neg_div, neg_neg]
  have hidentity (x : ℝ) (hx : 0 < x) : f x = A x * R x := by
    have hEq : S =ᶠ[𝓝 x] R := by
      filter_upwards [Ioi_mem_nhds hx] with t ht
      exact he t ht
    have hd := (hS x hx).unique ((hR x hx).congr_of_eventuallyEq hEq)
    dsimp [A] at *
    linarith
  have hpoly (x : ℝ) (hx : 0 < x) :
      k * (c*b*x+c*c*b-c*k-x) = 0 := by
    have hEq : f =ᶠ[𝓝 x] (fun t => A t * R t) := by
      filter_upwards [Ioi_mem_nhds hx] with t ht
      exact hidentity t ht
    have hd := (hf x hx).unique (((hA x hx).mul (hR x hx)).congr_of_eventuallyEq hEq)
    rw [hidentity x hx] at hd
    have hRp : 0 < R x := div_pos (hp (x+c) (by linarith)) (hp c hc)
    have hcancel : (k/x-b)*A x = k/(x+c)^2 + A x*(k/(x+c)-b) := by
      apply mul_right_cancel₀ hRp.ne'
      nlinarith [hd]
    dsimp [A] at hcancel
    calc
      k * (c*b*x+c*c*b-c*k-x) =
          ((k/x-b)*(b-k/(x+c)) - (k/(x+c)^2 + (b-k/(x+c))*(k/(x+c)-b))) *
            (x*(x+c)^2) := by
        field_simp [ne_of_gt hx, ne_of_gt (show 0 < x+c by linarith)]
        ring
      _ = 0 := by rw [hcancel, sub_self, zero_mul]
  by_cases hk : k = 0
  · exact Or.inl hk
  · have h1 := (mul_eq_zero.mp (hpoly 1 (by norm_num))).resolve_left hk
    have h2 := (mul_eq_zero.mp (hpoly 2 (by norm_num))).resolve_left hk
    have hcb : c*b = 1 := by nlinarith
    refine Or.inr ⟨?_, hcb⟩
    have hck : c*k = c := by nlinarith [h1, hcb]
    exact mul_left_cancel₀ hc.ne' (by simpa using hck)

/-- The actual Gamma survival for arbitrary positive shape and rate. -/
def gammaShapeSurvival (a b x : ℝ) : ℝ := (gammaMeasure a b (Ioi x)).toReal

theorem gamma_shape_density_integral (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ t : ℝ, gammaPDFReal a b t) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (gammaPDFReal_nonneg ha hb))
    (measurable_gammaPDFReal a b).aestronglyMeasurable]
  change (∫⁻ t : ℝ, gammaPDF a b t).toReal = 1
  rw [lintegral_gammaPDF_eq_one ha hb]
  norm_num

theorem gamma_shape_density_integrable (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Integrable (gammaPDFReal a b) :=
  Integrable.of_integral_ne_zero (by rw [gamma_shape_density_integral a b ha hb]; norm_num)

theorem gamma_shape_survival_integral (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) :
    gammaShapeSurvival a b x = ∫ t : ℝ in Ioi x, gammaPDFReal a b t := by
  rw [gammaShapeSurvival, gammaMeasure, withDensity_apply _ measurableSet_Ioi,
    integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall (gammaPDFReal_nonneg ha hb))
      (measurable_gammaPDFReal a b).aestronglyMeasurable.restrict]
  rfl

theorem gamma_shape_density_derivative (a b x : ℝ) (hx : 0 < x) :
    HasDerivAt (gammaPDFReal a b) (((a-1)/x-b)*gammaPDFReal a b x) x := by
  have hd := ((Real.hasDerivAt_rpow_const (p := a-1) (Or.inl hx.ne')).const_mul
    (b^a / Real.Gamma a)).mul (((hasDerivAt_id x).const_mul (-b)).exp)
  have hformula : gammaPDFReal a b =ᶠ[𝓝 x]
      (fun t => b^a / Real.Gamma a * t^(a-1) * Real.exp (-b*t)) := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    simp only [gammaPDFReal, if_pos ht.le, neg_mul]
  convert hd.congr_of_eventuallyEq hformula using 1
  rw [gammaPDFReal, if_pos hx.le, Real.rpow_sub_one hx.ne' (a-1)]
  simp only [id_eq, mul_one, neg_mul]
  ring

theorem gamma_shape_survival_derivative (a b x : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hx : 0 < x) :
    HasDerivAt (gammaShapeSurvival a b) (-gammaPDFReal a b x) x := by
  have hi := gamma_shape_density_integrable a b ha hb
  have hd := intervalIntegral.integral_hasDerivAt_right (a := 0) hi.intervalIntegrable
    (measurable_gammaPDFReal a b).stronglyMeasurable.stronglyMeasurableAtFilter
    (gamma_shape_density_derivative a b x hx).continuousAt
  have he : gammaShapeSurvival a b = fun y =>
      (∫ t : ℝ, gammaPDFReal a b t) -
        (∫ t : ℝ in Iic 0, gammaPDFReal a b t) - ∫ t : ℝ in (0 : ℝ)..y, gammaPDFReal a b t := by
    funext y
    rw [gamma_shape_survival_integral a b y ha hb]
    have hsum := intervalIntegral.integral_Iic_add_Ioi
      (hi.integrableOn (s := Iic y)) (hi.integrableOn (s := Ioi y))
    have hdiff := intervalIntegral.integral_Iic_sub_Iic
      (hi.integrableOn (s := Iic 0)) (hi.integrableOn (s := Iic y))
    linarith
  rw [he]
  exact hd.const_sub _

/-- Necessity in the manuscript's full positive-shape, positive-rate class. -/
theorem gamma_self_shift_necessary (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (he : ∀ x ≥ 0, gammaShapeSurvival a b x = gammaPDFReal a b (x+c)/gammaPDFReal a b c) :
    a = 1 ∨ a = 2 ∧ c = 1/b := by
  have hr := gamma_shift_ode_classification (gammaPDFReal a b) (gammaShapeSurvival a b)
    (a-1) b c hc (fun _ hx => gammaPDFReal_pos ha hb hx)
    (gamma_shape_density_derivative a b) (fun x hx => gamma_shape_survival_derivative a b x ha hb hx)
    (fun x hx => he x hx.le)
  rcases hr with hr | ⟨ha2, hcb⟩
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨by linarith, (eq_div_iff hb.ne').mpr hcb⟩

theorem gamma_shape_one_density (b x : ℝ) (hx : 0 ≤ x) :
    gammaPDFReal 1 b x = b * Real.exp (-(b*x)) := by
  norm_num [gammaPDFReal, if_pos hx]

theorem gamma_shape_two_density (b x : ℝ) (hx : 0 ≤ x) :
    gammaPDFReal 2 b x = b^2*x*Real.exp (-(b*x)) := by
  have hg : Real.Gamma 2 = 1 := by simp
  norm_num [gammaPDFReal, if_pos hx, hg, Real.rpow_two]

theorem gamma_shape_one_survival (b x : ℝ) (hb : 0 < b) (hx : 0 ≤ x) :
    gammaShapeSurvival 1 b x = Real.exp (-(b*x)) := by
  have hd : ∀ t ∈ Ici x, HasDerivAt (fun t => -Real.exp (-(b*t)))
      (gammaPDFReal 1 b t) t := by
    intro t ht
    rw [gamma_shape_one_density b t (hx.trans ht)]
    convert (((hasDerivAt_id t).const_mul b).neg.exp).neg using 1
    simp only [id_eq, mul_one, neg_mul, neg_neg]
    ring
  have hl : Tendsto (fun t : ℝ => -Real.exp (-(b*t))) atTop (𝓝 0) := by
    simpa only [neg_zero, Function.comp_def] using
      (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
        (tendsto_id.const_mul_atTop hb))).neg
  have he := integral_Ioi_of_hasDerivAt_of_tendsto' hd
    (gamma_shape_density_integrable 1 b (by norm_num) hb).integrableOn hl
  rw [gamma_shape_survival_integral 1 b x (by norm_num) hb]
  simpa using he

theorem gamma_shape_two_survival (b x : ℝ) (hb : 0 < b) (hx : 0 ≤ x) :
    gammaShapeSurvival 2 b x = gammaSurvival (b*x) := by
  have hd : ∀ t ∈ Ici x, HasDerivAt (fun t => -gammaSurvival (b*t))
      (gammaPDFReal 2 b t) t := by
    intro t ht
    rw [gamma_shape_two_density b t (hx.trans ht)]
    convert ((gamma_survival_derivative (b*t)).comp t
      ((hasDerivAt_id t).const_mul b)).neg using 1
    simp only [id_eq, mul_one, SigmaPresentations.density]
    ring
  have hl : Tendsto (fun t : ℝ => -gammaSurvival (b*t)) atTop (𝓝 0) := by
    simpa only [neg_zero, Function.comp_def] using
      (gamma_survival_tendsto.comp (tendsto_id.const_mul_atTop hb)).neg
  have he := integral_Ioi_of_hasDerivAt_of_tendsto' hd
    (gamma_shape_density_integrable 2 b (by norm_num) hb).integrableOn hl
  rw [gamma_shape_survival_integral 2 b x (by norm_num) hb]
  simpa using he

theorem gamma_self_shift_iff (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (∀ x ≥ 0, gammaShapeSurvival a b x = gammaPDFReal a b (x+c)/gammaPDFReal a b c) ↔
      a = 1 ∨ a = 2 ∧ c = 1/b := by
  refine ⟨gamma_self_shift_necessary a b c ha hb hc, ?_⟩
  intro h x hx
  rcases h with rfl | ⟨rfl, rfl⟩
  · rw [gamma_shape_one_survival b x hb hx,
      gamma_shape_one_density b (x+c) (by linarith), gamma_shape_one_density b c hc.le]
    rw [mul_add, neg_add, Real.exp_add]
    field_simp
    ring
  · rw [gamma_shape_two_survival b x hb hx,
      gamma_shape_two_density b (x+1/b) (by positivity),
      gamma_shape_two_density b (1/b) (by positivity)]
    unfold gammaSurvival
    simp only [mul_add, neg_add, Real.exp_add]
    field_simp [hb.ne']
    ring

end
end Sigma
