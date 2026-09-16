import SigmaZeroFamily
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

namespace Sigma
noncomputable section
open Filter Set
open scoped Topology

theorem positive_real_log_analytic {t : ℝ} (ht : 0 < t) : AnalyticAt ℝ Real.log t := by
  have ha : AnalyticAt ℝ Complex.log (t : ℂ) :=
    (analyticAt_clog (Complex.ofReal_mem_slitPlane.mpr ht)).restrictScalars
  have hb := ha.comp (Complex.ofRealCLM.analyticAt t)
  have hc := (Complex.reCLM.analyticAt (Complex.log (t : ℂ))).comp
    (f := fun x : ℝ => Complex.log (x : ℂ)) hb
  simpa only [Function.comp_def, Complex.reCLM_apply, Complex.ofRealCLM_apply,
    Complex.log_ofReal_re] using hc

theorem positive_real_rpow_analytic (p : ℝ) {t : ℝ} (ht : 0 < t) :
    AnalyticAt ℝ (fun x : ℝ => x^p) t := by
  have ha := ((positive_real_log_analytic ht).mul (analyticAt_const (v := p))).rexp
  apply ha.congr
  filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
  exact (Real.rpow_def_of_pos hx p).symm

theorem zeroFamily_analytic {k t : ℝ} (ht : 0 < t+k) :
    AnalyticAt ℝ (zeroFamily k) t := by
  have ha := (positive_real_rpow_analytic (-(k+1)) ht).comp (f := fun x : ℝ => x+k)
    ((analyticAt_id (𝕜 := ℝ)).add (analyticAt_const (v := k)))
  exact ((analyticAt_const.mul analyticAt_id).mul ha)

theorem zeroFamily_smooth {k : ℝ} : ContDiffOn ℝ ⊤ (zeroFamily k) (Ioi (-k)) := by
  intro t ht
  change -k < t at ht
  exact (zeroFamily_analytic (by linarith : 0 < t+k)).contDiffAt.contDiffWithinAt

end
end Sigma
