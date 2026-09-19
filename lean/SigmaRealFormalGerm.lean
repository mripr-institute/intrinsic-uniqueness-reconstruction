import SigmaFormalExpLogBaseChange
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Normed.Field.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential

namespace Sigma
noncomputable section
open PowerSeries Filter
open scoped Topology BigOperators

/-- A native analytic expansion at zero with exactly the coefficients of the
specified formal power series. -/
def HasRealFormalGerm (f : ℝ → ℝ) (F : PowerSeries ℝ) : Prop :=
  HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℝ (fun n => coeff ℝ n F)) 0

theorem real_formal_germ_iff (f : ℝ → ℝ) (F : PowerSeries ℝ) :
    HasRealFormalGerm f F ↔
      ∀ᶠ z in 𝓝 (0:ℝ), HasSum (fun n => coeff ℝ n F*z^n) (f z) := by
  rw [HasRealFormalGerm, hasFPowerSeriesAt_iff]
  simp [FormalMultilinearSeries.coeff, FormalMultilinearSeries.ofScalars, mul_comm,
    Pi.one_def, List.ofFn_const]

theorem analytic_has_real_formal_germ (f : ℝ → ℝ) (hf : AnalyticAt ℝ f 0) :
    ∃ F : PowerSeries ℝ, HasRealFormalGerm f F := by
  obtain ⟨p,hp⟩ := hf
  refine ⟨PowerSeries.mk p.coeff, (real_formal_germ_iff _ _).mpr ?_⟩
  simpa [coeff_mk, smul_eq_mul, mul_comm] using hasFPowerSeriesAt_iff.mp hp

theorem real_formal_germ_unique {f : ℝ → ℝ} {F G : PowerSeries ℝ}
    (hF : HasRealFormalGerm f F) (hG : HasRealFormalGerm f G) : F=G := by
  have h := FormalMultilinearSeries.ofScalars_series_injective ℝ ℝ
    (hF.eq_formalMultilinearSeries hG)
  exact PowerSeries.ext (congrFun h)

theorem real_formal_germ_mul {f g : ℝ → ℝ} {F G : PowerSeries ℝ}
    (hf : HasRealFormalGerm f F) (hg : HasRealFormalGerm g G) :
    HasRealFormalGerm (fun x => f x*g x) (F*G) := by
  apply (real_formal_germ_iff _ _).mpr
  filter_upwards [(real_formal_germ_iff _ _).mp hf,
    (real_formal_germ_iff _ _).mp hg] with z hfz hgz
  have h := hasSum_sum_range_mul_of_summable_norm hfz.summable.norm hgz.summable.norm
  rw [hfz.tsum_eq,hgz.tsum_eq] at h
  convert h using 1
  funext n
  rw [coeff_mul, Finset.sum_mul]
  rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff ℝ i F*z^i*(coeff ℝ j G*z^j))]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j.1+j.2=n := Finset.mem_antidiagonal.mp hj
  rw [← hjn, pow_add]
  ring

theorem real_formal_germ_sub {f g : ℝ → ℝ} {F G : PowerSeries ℝ}
    (hf : HasRealFormalGerm f F) (hg : HasRealFormalGerm g G) :
    HasRealFormalGerm (fun x => f x-g x) (F-G) := by
  apply (real_formal_germ_iff _ _).mpr
  filter_upwards [(real_formal_germ_iff _ _).mp hf,
    (real_formal_germ_iff _ _).mp hg] with z hfz hgz
  simpa only [map_sub, sub_mul] using hfz.sub hgz

theorem real_formal_germ_const (a : ℝ) : HasRealFormalGerm (fun _ => a) (C ℝ a) := by
  apply (real_formal_germ_iff _ _).mpr
  exact Eventually.of_forall fun z => by
    convert (hasSum_ite_eq (0:ℕ) a) using 1
    funext n
    by_cases hn : n=0
    · simp [hn]
    · simp [coeff_C,hn]

theorem real_formal_germ_rescale {f : ℝ → ℝ} {F : PowerSeries ℝ}
    (hf : HasRealFormalGerm f F) (a : ℝ) :
    HasRealFormalGerm (fun x => f (a*x)) (rescale a F) := by
  apply (real_formal_germ_iff _ _).mpr
  have hc : Tendsto (fun x : ℝ => a*x) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_const.mul continuous_id).tendsto (0:ℝ)
  filter_upwards [hc.eventually ((real_formal_germ_iff _ _).mp hf)] with z hz
  simpa only [coeff_rescale, mul_pow, mul_left_comm, mul_assoc] using hz

theorem real_formal_germ_exp (a : ℝ) :
    HasRealFormalGerm (fun x => Real.exp (a*x)) (formalExponential ℝ a) := by
  apply (real_formal_germ_iff _ _).mpr
  exact Eventually.of_forall fun z => by
    simpa [NormedSpace.expSeries_apply_eq, Real.exp_eq_exp_ℝ,
      formalExponential, coeff_rescale, coeff_exp, mul_pow, div_eq_mul_inv,
      mul_left_comm, mul_assoc] using (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (a*z))

theorem real_formal_germ_X : HasRealFormalGerm id (X:PowerSeries ℝ) := by
  apply (real_formal_germ_iff _ _).mpr
  exact Eventually.of_forall fun z => by
    convert (hasSum_ite_eq (1:ℕ) z) using 1
    funext n
    by_cases hn : n=1
    · simp [hn]
    · simp [coeff_X,hn]

theorem real_formal_germ_dslope {f : ℝ → ℝ} {F : PowerSeries ℝ}
    (hf : HasRealFormalGerm f F) :
    HasRealFormalGerm (dslope f 0) (PowerSeries.mk fun n => coeff ℝ (n+1) F) := by
  apply (real_formal_germ_iff _ _).mpr
  have h := hasFPowerSeriesAt_iff.mp hf.has_fpower_series_dslope_fslope
  simp only [FormalMultilinearSeries.coeff_fslope] at h
  simpa [FormalMultilinearSeries.coeff,
    FormalMultilinearSeries.ofScalars, mul_comm, Pi.one_def, List.ofFn_const] using h

theorem real_formal_germ_congr {f g : ℝ → ℝ} {F : PowerSeries ℝ}
    (hf : HasRealFormalGerm f F) (he : f =ᶠ[𝓝 0] g) : HasRealFormalGerm g F := by
  apply (real_formal_germ_iff _ _).mpr
  filter_upwards [(real_formal_germ_iff _ _).mp hf, he] with x hx heq
  rwa [← heq]

theorem real_formal_germ_constant {f : ℝ → ℝ} {F : PowerSeries ℝ}
    (hf : HasRealFormalGerm f F) : constantCoeff ℝ F=f 0 := by
  have h := hf.coeff_zero 1
  simpa [FormalMultilinearSeries.ofScalars, coeff_zero_eq_constantCoeff_apply] using h

/-- Multiplicative unit inversion of analytic germs agrees with the native
formal power-series inverse. Only nonvanishing at the expansion point is
required; zeros elsewhere impose no additional local assumption. -/
theorem real_formal_germ_inv {f : ℝ → ℝ} {F : PowerSeries ℝ}
    (hf : HasRealFormalGerm f F) (h0 : f 0 ≠ 0) :
    HasRealFormalGerm (fun x => (f x)⁻¹) F⁻¹ := by
  obtain ⟨G,hG⟩ := analytic_has_real_formal_germ _ (hf.analyticAt.inv h0)
  have hprod := real_formal_germ_mul hG hf
  have he : (fun x => (f x)⁻¹*f x) =ᶠ[𝓝 0] (fun _ => 1) := by
    filter_upwards [hf.continuousAt.eventually_ne h0] with x hx
    exact inv_mul_cancel₀ hx
  have hp := real_formal_germ_congr hprod he
  have heq : G*F=1 := by
    simpa using real_formal_germ_unique hp (real_formal_germ_const 1)
  have hid : G=F⁻¹ := (PowerSeries.eq_inv_iff_mul_eq_one
    (by rw [real_formal_germ_constant hf]; exact h0)).mpr heq
  rwa [hid] at hG

end
end Sigma
