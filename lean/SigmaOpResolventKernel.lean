import SigmaOpHeatKernelNorm
import SigmaL2BochnerKernel
import SigmaOpHeatResolvent

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
attribute [local instance] Measure.Subtype.measureSpace

local instance : SigmaFinite (volume : Measure (Set.Ioi (0:ℝ))) := by
  apply SigmaFinite.of_map _ measurable_subtype_coe.aemeasurable
  change SigmaFinite ((Measure.comap Subtype.val (volume : Measure ℝ)).map Subtype.val)
  rw [map_comap_subtype_coe measurableSet_Ioi]
  infer_instance

theorem laguerre_heat_kernel_joint_measurable :
    Measurable (fun z : Set.Ioi (0:ℝ) × (ℝ × ℝ) =>
      laguerreHeatKernel z.1.val z.2.1 z.2.2) := by
  have hb : Measurable (fun z : Set.Ioi (0:ℝ) × (ℝ × ℝ) =>
      modifiedBesselI1 (2*Real.sqrt (Real.exp (-z.1.val)*z.2.1*z.2.2)/
        (1-Real.exp (-z.1.val)))) :=
    modified_bessel_i1_continuous.measurable.comp (by fun_prop)
  unfold laguerreHeatKernel laguerreHeatKernelClosed
  apply Measurable.ite (measurableSet_lt measurable_const (measurable_snd.snd))
  · exact Measurable.mul (by fun_prop) hb
  · exact measurable_const

theorem laguerre_heat_kernel_vector_coe (t : Set.Ioi (0:ℝ)) :
    (laguerreHeatKernelVector t : ℝ × ℝ → ℝ) =ᵐ[gammaProbability.prod gammaProbability]
      fun z => laguerreHeatKernel t.val z.1 z.2 := by
  rw [laguerreHeatKernelVector, ← laguerre_heat_kernel_product_l2_eq_spectral t.property]
  exact Memℒp.coeFn_toLp _

def laguerreLaplaceKernelVector (a : ℝ) (k : ℕ) : LaguerreProductHilbert :=
  ∫ t : Set.Ioi (0:ℝ), (t.val^k*Real.exp (-a*t.val)) • laguerreHeatKernelVector t

/-- k=0 is the first resolvent kernel; k=1 is the squared resolvent kernel. -/
def laguerreLaplaceKernel (a : ℝ) (k : ℕ) (x y : ℝ) : ℝ :=
  ∫ t : Set.Ioi (0:ℝ), t.val^k*Real.exp (-a*t.val)*laguerreHeatKernel t.val x y

theorem laguerre_laplace_kernel_joint_stronglyMeasurable (a : ℝ) (k : ℕ) :
    StronglyMeasurable (fun z : Set.Ioi (0:ℝ) × (ℝ × ℝ) =>
      z.1.val^k*Real.exp (-a*z.1.val)*laguerreHeatKernel z.1.val z.2.1 z.2.2) :=
  (Measurable.mul (by fun_prop) laguerre_heat_kernel_joint_measurable).stronglyMeasurable

theorem laguerre_laplace_kernel_weighted_coe (a : ℝ) (k : ℕ) (t : Set.Ioi (0:ℝ)) :
    (((t.val^k*Real.exp (-a*t.val)) • laguerreHeatKernelVector t : LaguerreProductHilbert) :
      ℝ × ℝ → ℝ)
      =ᵐ[gammaProbability.prod gammaProbability]
        fun z => t.val^k*Real.exp (-a*t.val)*laguerreHeatKernel t.val z.1 z.2 := by
  filter_upwards [Lp.coeFn_smul (t.val^k*Real.exp (-a*t.val)) (laguerreHeatKernelVector t),
    laguerre_heat_kernel_vector_coe t] with z hs he
  rw [hs, Pi.smul_apply, smul_eq_mul, he]

/-- The kernel-valued Bochner integral equals the paper's literal Laplace
integral almost everywhere in the weighted product space. -/
theorem laguerre_laplace_kernel_vector_coe (a : ℝ) (ha : 0 < a) (k : ℕ) :
    (laguerreLaplaceKernelVector a k : ℝ × ℝ → ℝ) =ᵐ[
      gammaProbability.prod gammaProbability] fun z => laguerreLaplaceKernel a k z.1 z.2 :=
  l2_bochner_integral_representative _ (laguerre_heat_kernel_weighted_integrable a ha k) _
    (laguerre_laplace_kernel_joint_stronglyMeasurable a k)
    (laguerre_laplace_kernel_weighted_coe a k)

/-- Existence in weighted product L² is proved for the literal kernel. -/
theorem laguerre_laplace_kernel_mem_l2 (a : ℝ) (ha : 0 < a) (k : ℕ) :
    Memℒp (fun z : ℝ × ℝ => laguerreLaplaceKernel a k z.1 z.2) 2
      (gammaProbability.prod gammaProbability) :=
  (memℒp_congr_ae (laguerre_laplace_kernel_vector_coe a ha k)).mp
    (Lp.memℒp (laguerreLaplaceKernelVector a k))

/-- The time integrals are genuinely finite almost everywhere; their values
are not merely the default value of an undefined Bochner integral. -/
theorem laguerre_laplace_kernel_integrable_ae (a : ℝ) (ha : 0 < a) (k : ℕ) :
    ∀ᵐ z : ℝ × ℝ ∂gammaProbability.prod gammaProbability,
      Integrable (fun t : Set.Ioi (0:ℝ) =>
        t.val^k*Real.exp (-a*t.val)*laguerreHeatKernel t.val z.1 z.2) :=
  (l2_representatives_joint_integrable _ (laguerre_heat_kernel_weighted_integrable a ha k)
    (fun t z => t.val^k*Real.exp (-a*t.val)*laguerreHeatKernel t.val z.1 z.2)
    (laguerre_laplace_kernel_joint_stronglyMeasurable a k)
    (laguerre_laplace_kernel_weighted_coe a k)).prod_left_ae

theorem laguerre_laplace_kernel_nonnegative (a : ℝ) (k : ℕ) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) : 0 ≤ laguerreLaplaceKernel a k x y := by
  apply integral_nonneg
  intro t
  exact mul_nonneg (mul_nonneg (pow_nonneg t.property.le k) (Real.exp_pos _).le)
    (laguerre_heat_kernel_pos t.property hx hy).le

theorem laguerre_laplace_kernel_eq_setIntegral (a : ℝ) (k : ℕ) (x y : ℝ) :
    laguerreLaplaceKernel a k x y =
      ∫ t : ℝ in Ioi 0, t^k*Real.exp (-a*t)*laguerreHeatKernel t x y :=
  integral_subtype (s := Ioi (0:ℝ)) measurableSet_Ioi
    (fun t : ℝ => t^k*Real.exp (-a*t)*laguerreHeatKernel t x y)

/-- Fubini transfers the kernel-valued integral to its action on arbitrary
complex L² inputs. The final first/squared-resolvent theorems below discharge
the vector-integrability premise with the established strong heat integrals. -/
theorem laguerre_laplace_kernel_action (a : ℝ) (ha : 0 < a) (k : ℕ)
    (f : LaguerreWeightedHilbert)
    (hv : Integrable (fun t : Ioi (0:ℝ) =>
      ((t.val^k*Real.exp (-a*t.val):ℝ):ℂ) • laguerreHeatOperator t.val t.property.le f)) :
    (fun x : ℝ => ∫ y : ℝ, (laguerreLaplaceKernel a k x y:ℂ)*f y ∂gammaProbability)
      =ᵐ[gammaProbability]
      ((∫ t : Ioi (0:ℝ), ((t.val^k*Real.exp (-a*t.val):ℝ):ℂ) •
        laguerreHeatOperator t.val t.property.le f : LaguerreWeightedHilbert) : ℝ → ℂ) := by
  let F : Ioi (0:ℝ) → ℝ × ℝ → ℝ := fun t z =>
    t.val^k*Real.exp (-a*t.val)*laguerreHeatKernel t.val z.1 z.2
  let Q : Ioi (0:ℝ) × (ℝ × ℝ) → ℂ := fun z => (F z.1 z.2:ℂ)*f z.2.2
  let G : Ioi (0:ℝ) → ℝ → ℂ := fun t x => ∫ y, Q (t,x,y) ∂gammaProbability
  have hF := laguerre_laplace_kernel_joint_stronglyMeasurable a k
  have hsnd : MeasurePreserving (Prod.snd : ℝ × ℝ → ℝ)
      (gammaProbability.prod gammaProbability) gammaProbability :=
    ⟨measurable_snd, by simp⟩
  have hfm : StronglyMeasurable (fun z : ℝ × ℝ => f z.2) :=
    (Lp.stronglyMeasurable f).comp_measurable measurable_snd
  have hQ : Integrable Q (volume.prod (gammaProbability.prod gammaProbability)) :=
    l2_kernel_input_joint_integrable _ (laguerre_heat_kernel_weighted_integrable a ha k)
      F hF (laguerre_laplace_kernel_weighted_coe a k)
      (fun z => f z.2) ((Lp.memℒp f).comp_measurePreserving hsnd) hfm
  have hQm : StronglyMeasurable Q :=
    (Complex.continuous_ofReal.comp_stronglyMeasurable hF).mul
      (hfm.comp_measurable measurable_snd)
  have hG : StronglyMeasurable (Function.uncurry G) := by
    have hh : StronglyMeasurable (fun z : (Ioi (0:ℝ) × ℝ) × ℝ => Q (z.1.1,z.1.2,z.2)) :=
      hQm.comp_measurable (by fun_prop)
    exact hh.integral_prod_right'
  have hrep (t : Ioi (0:ℝ)) :
      ((((t.val^k*Real.exp (-a*t.val):ℝ):ℂ) •
        laguerreHeatOperator t.val t.property.le f : LaguerreWeightedHilbert) : ℝ → ℂ)
        =ᵐ[gammaProbability] G t := by
    filter_upwards [Lp.coeFn_smul (((t.val^k*Real.exp (-a*t.val):ℝ):ℂ))
      (laguerreHeatOperator t.val t.property.le f),
      laguerre_heat_kernel_integral_eq_operator t.property f] with x hs he
    rw [hs, Pi.smul_apply, smul_eq_mul, ← he]
    dsimp [G, Q, F]
    rw [← integral_mul_left]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by push_cast; ring
  have hB := l2_bochner_integral_representative _ hv G hG hrep
  have hswap := (integrable_swap_first_two hQ).prod_right_ae
  filter_upwards [hB, hswap] with x hx hxi
  rw [hx]
  change (∫ y : ℝ, (laguerreLaplaceKernel a k x y:ℂ)*f y ∂gammaProbability) =
    ∫ t : Ioi (0:ℝ), ∫ y : ℝ, Q (t,x,y) ∂gammaProbability
  rw [integral_integral_swap hxi]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  dsimp [Q, F, laguerreLaplaceKernel]
  rw [integral_mul_right]
  congr 1
  exact integral_ofReal.symm

/-- The first Laplace kernel represents the full native resolvent on every
complex Gamma-weighted L² vector. -/
theorem laguerre_resolvent_kernel_action (a : ℝ) (ha : 0 < a)
    (f : LaguerreWeightedHilbert) :
    (fun x : ℝ => ∫ y : ℝ, (laguerreLaplaceKernel a 0 x y:ℂ)*f y ∂gammaProbability)
      =ᵐ[gammaProbability] (laguerreResolvent a ha f : ℝ → ℂ) := by
  have h := laguerre_laplace_kernel_action a ha 0 f
    (by simpa only [pow_zero, one_mul] using laguerre_heat_laplace_integrable a ha f)
  simpa only [pow_zero, one_mul, laguerre_heat_laplace_operator a ha f] using h

/-- The time-weighted Laplace kernel represents the full squared resolvent. -/
theorem laguerre_squared_resolvent_kernel_action (a : ℝ) (ha : 0 < a)
    (f : LaguerreWeightedHilbert) :
    (fun x : ℝ => ∫ y : ℝ, (laguerreLaplaceKernel a 1 x y:ℂ)*f y ∂gammaProbability)
      =ᵐ[gammaProbability] (laguerreSquaredResolvent a ha f : ℝ → ℂ) := by
  have h := laguerre_laplace_kernel_action a ha 1 f
    (by simpa only [pow_one, Complex.ofReal_mul] using laguerre_heat_time_laplace_integrable a ha f)
  simpa only [pow_one, Complex.ofReal_mul, laguerre_heat_time_laplace_operator a ha f] using h

end
end Sigma
