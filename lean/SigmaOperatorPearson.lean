import SigmaOperators
import SigmaProbODE
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

/-- The standard integral characterization of real local absolute continuity:
on every compact positive interval there is an L1 a.e.-derivative representative
whose integral recovers the function. This category definition is independent
of Pearson, positivity, normalization, and the target density. Mathlib's pinned
version has no separate function-absolute-continuity predicate. -/
def LocallyIntegralAbsolutelyContinuousPositive (w : ℝ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 < a → a < b → ∃ g : ℝ → ℝ,
    IntegrableOn g (Icc a b) volume ∧
      (∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt w (g t) t) ∧
      ∀ t ∈ Icc a b, w t = w a + ∫ s : ℝ in a..t, g s

theorem local_integral_ac_continuousOn (w : ℝ → ℝ)
    (hw : LocallyIntegralAbsolutelyContinuousPositive w)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) : ContinuousOn w (Icc a b) := by
  obtain ⟨g, hg, _, he⟩ := hw a b ha hab
  have hg' : IntegrableOn g (uIcc a b) volume := by simpa only [uIcc_of_le hab.le] using hg
  have hcp := intervalIntegral.continuousOn_primitive_interval hg'
  have hc : ContinuousOn (fun x => w a + ∫ s : ℝ in a..x, g s) (Icc a b) :=
    continuousOn_const.add (by simpa only [uIcc_of_le hab.le] using hcp)
  exact hc.congr he

theorem local_integral_ac_continuousAt (w : ℝ → ℝ)
    (hw : LocallyIntegralAbsolutelyContinuousPositive w) {t : ℝ} (ht : 0 < t) :
    ContinuousAt w t := by
  have ha : 0 < t/2 := by positivity
  have hab : t/2 < t+1 := by linarith
  exact (local_integral_ac_continuousOn w hw (t/2) (t+1) ha hab).continuousAt
    (Icc_mem_nhds (by linarith) (by linarith))

/-- The a.e. Pearson equation upgrades the local-AC representative to a
classically differentiable solution everywhere on the positive ray. -/
theorem local_ac_pearson_hasDerivAt (w : ℝ → ℝ)
    (hw : LocallyIntegralAbsolutelyContinuousPositive w)
    (hP : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)),
      HasDerivAt (fun s => s*w s) ((2-t)*w t) t)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt w ((1-t)*w t/t) t := by
  let a : ℝ := t/2
  let b : ℝ := t+1
  have ha : 0 < a := by dsimp [a]; positivity
  have hat : a < t := by dsimp [a]; linarith
  have htb : t < b := by dsimp [b]; linarith
  have hab : a < b := hat.trans htb
  obtain ⟨g, hg, hgd, hrep⟩ := hw a b ha hab
  have hc := local_integral_ac_continuousOn w hw a b ha hab
  let R : ℝ → ℝ := fun s => (1-s)*w s/s
  have hRc : ContinuousOn R (Icc a b) :=
    ((continuousOn_const.sub continuousOn_id).mul hc).div continuousOn_id
      (fun s hs => ne_of_gt (ha.trans_le hs.1))
  have hPg := (ae_restrict_iff' measurableSet_Ioi).mp hP
  have hgg := (ae_restrict_iff' measurableSet_Ioo).mp hgd
  have hgeq : ∀ᵐ s : ℝ ∂volume, s ∈ Icc a b → g s = R s := by
    have hna : ∀ᵐ s : ℝ ∂volume, s ≠ a := by simp [ae_iff]
    have hnb : ∀ᵐ s : ℝ ∂volume, s ≠ b := by simp [ae_iff]
    filter_upwards [hPg, hgg, hna, hnb] with s hps hgs hsa hsb hs
    have hsp : 0 < s := ha.trans_le hs.1
    have hsint : s ∈ Ioo a b := ⟨lt_of_le_of_ne hs.1 hsa.symm, lt_of_le_of_ne hs.2 hsb⟩
    have hd := ((hasDerivAt_id s).mul (hgs hsint)).unique (hps hsp)
    simp only [id_eq, one_mul] at hd
    dsimp [R]
    apply (eq_div_iff (ne_of_gt hsp)).mpr
    nlinarith
  have hnew : ∀ x ∈ Icc a b, w x = w a + ∫ s : ℝ in a..x, R s := by
    intro x hx
    rw [hrep x hx]
    congr 1
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hgeq] with s hgs hs
    rw [uIoc_of_le hx.1] at hs
    exact hgs ⟨hs.1.le, hs.2.trans hx.2⟩
  have hi : IntervalIntegrable R volume a t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hat.le]
    exact hRc.mono (Icc_subset_Icc_right htb.le)
  have hRt : ContinuousAt R t := hRc.continuousAt (Icc_mem_nhds hat htb)
  have hRm : StronglyMeasurableAtFilter R (nhds t) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hRc.mono Ioo_subset_Icc_self) t ⟨hat, htb⟩
  have hd := (intervalIntegral.integral_hasDerivAt_right hi hRm hRt).const_add (w a)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds hat htb] with x hx
  exact hnew x hx

theorem differentiable_pearson_density_family (w : ℝ → ℝ)
    (hd : ∀ t > 0, HasDerivAt w ((1-t)*w t/t) t) :
    ∃ C : ℝ, ∀ t > 0, w t = C*SigmaPresentations.density t := by
  let G : ℝ → ℝ := fun t => Real.exp t*w t/t
  have hG : ∀ t > 0, HasDerivAt G 0 t := by
    intro t ht
    convert ((Real.hasDerivAt_exp t).mul (hd t ht)).div (hasDerivAt_id t) (ne_of_gt ht) using 1
    field_simp
    ring
  let C : ℝ := G 1
  have hC : ∀ t > 0, G t = C :=
    equal_of_equal_derivatives G (fun _ => C)
      (fun t ht => (hG t ht).differentiableAt)
      (fun _ _ => differentiableAt_const _)
      (by intro t ht; rw [(hG t ht).deriv]; simp) rfl
  refine ⟨C, ?_⟩
  intro t ht
  have he := hC t ht
  dsimp [G] at he
  have he' := (div_eq_iff (ne_of_gt ht)).mp he
  rw [SigmaPresentations.density, Real.exp_neg, ← mul_assoc]
  apply (eq_mul_inv_iff_mul_eq₀ (Real.exp_ne_zero t)).mpr
  simpa only [mul_comm] using he'

/-- Exact normalized Pearson inverse under local absolute continuity only;
the everywhere derivative is a conclusion supplied by the preceding theorem. -/
theorem local_ac_pearson_density_unique (w : ℝ → ℝ)
    (hw : LocallyIntegralAbsolutelyContinuousPositive w)
    (hP : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)),
      HasDerivAt (fun s => s*w s) ((2-t)*w t) t)
    (hmass : (∫ t : ℝ in Ioi 0, w t) = 1) :
    ∀ t > 0, w t = SigmaPresentations.density t := by
  obtain ⟨C, hC⟩ := differentiable_pearson_density_family w (local_ac_pearson_hasDerivAt w hw hP)
  have hCi : (∫ t : ℝ in Ioi 0, w t) = C := by
    calc
      _ = ∫ t : ℝ in Ioi 0, C*SigmaPresentations.density t :=
        setIntegral_congr_fun measurableSet_Ioi hC
      _ = C := by rw [integral_mul_left, intrinsic_density_integral_one, mul_one]
  have hC1 : C = 1 := hCi.symm.trans hmass
  intro t ht
  simpa only [hC1, one_mul] using hC t ht

theorem local_ac_pearson_density_integrable (w : ℝ → ℝ)
    (hmass : (∫ t : ℝ in Ioi 0, w t) = 1) : IntegrableOn w (Ioi (0:ℝ)) := by
  exact Integrable.of_integral_ne_zero (by rw [hmass]; norm_num)

theorem local_ac_pearson_weight_measure (w : ℝ → ℝ)
    (hw : LocallyIntegralAbsolutelyContinuousPositive w)
    (hP : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)),
      HasDerivAt (fun s => s*w s) ((2-t)*w t) t)
    (hmass : (∫ t : ℝ in Ioi 0, w t) = 1) :
    volume.withDensity ((Ioi (0:ℝ)).indicator (fun t => ENNReal.ofReal (w t))) =
      gammaProbability := by
  have he := local_ac_pearson_density_unique w hw hP hmass
  unfold gammaProbability ProbabilityTheory.gammaMeasure
  congr 1
  funext t
  rw [ProbabilityTheory.gammaPDF, gamma_pdf_intrinsic]
  by_cases ht : 0 < t
  · simp [ht, ht.le, he t ht]
  · by_cases h0 : t = 0
    · subst t
      simp [SigmaPresentations.density]
    · have hn : ¬ 0 ≤ t := by intro h; exact h0 (le_antisymm (le_of_not_gt ht) h)
      simp [ht, hn]

/-- At a common differentiability point, equality almost everywhere in an
open neighborhood forces equality of the derivatives. This is the needed
transport lemma for coefficients identified only almost everywhere. -/
theorem ae_equal_positive_derivative_unique (f g : ℝ → ℝ) (f' g' x : ℝ)
    (hx : 0 < x) (he : ∀ᵐ t : ℝ ∂volume, 0 < t → f t = g t)
    (hval : f x = g x) (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) : f' = g' := by
  let S : Set ℝ := {t | t ≠ x ∧ (0 < t → f t = g t)}
  have hSae : ∀ᵐ t : ℝ ∂volume, t ∈ S := by
    have hn : ∀ᵐ t : ℝ ∂volume, t ≠ x := by simp [ae_iff]
    filter_upwards [hn, he] with t hne ht
    exact ⟨hne, ht⟩
  have hS : Dense S := Measure.dense_of_ae hSae
  haveI : NeBot (nhdsWithin x S) := mem_closure_iff_nhdsWithin_neBot.mp (hS x)
  have hsub : nhdsWithin x S ≤ nhdsWithin x ({x}ᶜ) :=
    nhdsWithin_mono x (fun t ht => ht.1)
  have hfe := (hasDerivAt_iff_tendsto_slope.mp hf).mono_left hsub
  have hge := (hasDerivAt_iff_tendsto_slope.mp hg).mono_left hsub
  have heq : slope f x =ᶠ[nhdsWithin x S] slope g x := by
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds hx)] with t ht htp
    simp only [slope, hval, ht.2 htp]
  exact tendsto_nhds_unique hfe (hge.congr' heq.symm)

theorem local_integral_ac_ae_differentiable (w : ℝ → ℝ)
    (hw : LocallyIntegralAbsolutelyContinuousPositive w) :
    ∀ᵐ t : ℝ ∂volume, 0 < t → DifferentiableAt ℝ w t := by
  have hh (N : ℕ) : ∀ᵐ t : ℝ ∂volume,
      t ∈ Ioo (1/((N:ℝ)+2)) ((N:ℝ)+2) → DifferentiableAt ℝ w t := by
    have hn : 0 ≤ (N:ℝ) := by positivity
    have hb : 0 < (N:ℝ)+2 := by linarith
    have hab : 1/((N:ℝ)+2) < (N:ℝ)+2 := (div_lt_iff₀ hb).mpr (by nlinarith)
    obtain ⟨g, _, hg, _⟩ := hw (1/((N:ℝ)+2)) ((N:ℝ)+2) (by positivity) hab
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mp hg] with t ht hmem
    exact (ht hmem).differentiableAt
  filter_upwards [ae_all_iff.mpr hh] with t ht hpos
  obtain ⟨N, hN⟩ := exists_nat_gt (max t (1/t))
  have hn : 0 ≤ (N:ℝ) := by positivity
  have hupper : t < (N:ℝ)+2 := (lt_of_le_of_lt (le_max_left _ _) hN).trans (by linarith)
  have hrec : 1/t < (N:ℝ)+2 := (lt_of_le_of_lt (le_max_right _ _) hN).trans (by linarith)
  have hlower : 1/((N:ℝ)+2) < t := by
    apply (div_lt_iff₀ (by linarith : 0 < (N:ℝ)+2)).mpr
    have h := (div_lt_iff₀ hpos).mp hrec
    nlinarith
  exact ht N ⟨hlower, hupper⟩

theorem local_ac_pearson_ae_coefficients (a b w : ℝ → ℝ)
    (hw : LocallyIntegralAbsolutelyContinuousPositive w)
    (hab : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), a t = t ∧ b t = 2-t)
    (hP : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)),
      HasDerivAt (fun s => a s*w s) (b t*w t) t) :
    ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)),
      HasDerivAt (fun s => s*w s) ((2-t)*w t) t := by
  have hc := (ae_restrict_iff' measurableSet_Ioi).mp hab
  have hp := (ae_restrict_iff' measurableSet_Ioi).mp hP
  have he : ∀ᵐ t : ℝ ∂volume, 0 < t → a t*w t = t*w t := by
    filter_upwards [hc] with t ht hpos
    rw [(ht hpos).1]
  apply (ae_restrict_iff' measurableSet_Ioi).mpr
  filter_upwards [hc, hp, local_integral_ac_ae_differentiable w hw] with t hct hpt hd ht
  have hdw := (hasDerivAt_id t).mul (hd ht).hasDerivAt
  have heder := ae_equal_positive_derivative_unique (fun s => a s*w s) (fun s => s*w s)
    (b t*w t) (w t+t*deriv w t) t ht he
    (by change a t*w t = t*w t; rw [(hct ht).1]) (hpt ht)
    (by simpa only [id_eq, one_mul] using hdw)
  rw [(hct ht).2] at heder
  simpa only [id_eq, one_mul, ← heder] using hdw

theorem operator_two_probe_pearson_inverse_ae (a b w : ℝ → ℝ)
    (hw : LocallyIntegralAbsolutelyContinuousPositive w)
    (hmass : (∫ t : ℝ in Ioi 0, w t) = 1)
    (hl : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), opExpression a b opLinearProbe t = 2-t)
    (hq : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), opExpression a b opQuadraticProbe t = t^2-6*t+6)
    (hP : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)),
      HasDerivAt (fun s => a s*w s) (b t*w t) t) :
    (∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), a t = t ∧ b t = 2-t) ∧
      (∀ t > 0, w t = SigmaPresentations.density t) ∧
      volume.withDensity ((Ioi (0:ℝ)).indicator (fun t => ENNReal.ofReal (w t))) = gammaProbability := by
  have hc := (operator_two_probe_ae_iff (volume.restrict (Ioi (0:ℝ))) a b).mp ⟨hl, hq⟩
  have hp := local_ac_pearson_ae_coefficients a b w hw hc hP
  exact ⟨hc, local_ac_pearson_density_unique w hw hp hmass,
    local_ac_pearson_weight_measure w hw hp hmass⟩

theorem operator_two_probe_pearson_inverse (a b w : ℝ → ℝ)
    (hw : LocallyIntegralAbsolutelyContinuousPositive w)
    (hmass : (∫ t : ℝ in Ioi 0, w t) = 1)
    (hl : ∀ t > 0, opExpression a b opLinearProbe t = 2-t)
    (hq : ∀ t > 0, opExpression a b opQuadraticProbe t = t^2-6*t+6)
    (hP : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)),
      HasDerivAt (fun s => a s*w s) (b t*w t) t) :
    (∀ t > 0, a t = t ∧ b t = 2-t) ∧
      (∀ t > 0, w t = SigmaPresentations.density t) ∧
      volume.withDensity ((Ioi (0:ℝ)).indicator (fun t => ENNReal.ofReal (w t))) = gammaProbability := by
  have hc := (operator_two_probe_iff a b).mp ⟨hl, hq⟩
  have hcae : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), a t = t ∧ b t = 2-t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hc t ht
  have hp := local_ac_pearson_ae_coefficients a b w hw hcae hP
  exact ⟨hc, local_ac_pearson_density_unique w hw hp hmass,
    local_ac_pearson_weight_measure w hw hp hmass⟩

theorem canonical_density_local_integral_ac :
    LocallyIntegralAbsolutelyContinuousPositive SigmaPresentations.density := by
  let g : ℝ → ℝ := fun t => (1-t)*Real.exp (-t)
  have hd (t : ℝ) : HasDerivAt SigmaPresentations.density (g t) t := by
    convert (hasDerivAt_id t).mul ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)) using 1
    dsimp [g]
    ring
  have hg : Continuous g := by dsimp [g]; fun_prop
  intro a b _ hab
  refine ⟨g, hg.integrableOn_Icc, Eventually.of_forall hd, ?_⟩
  intro t _
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hd x) (hg.intervalIntegrable a t)
  linarith

theorem operator_canonical_pearson_realization :
    LocallyIntegralAbsolutelyContinuousPositive SigmaPresentations.density ∧
      (∀ t > 0, 0 < SigmaPresentations.density t) ∧
      (∫ t : ℝ in Ioi 0, SigmaPresentations.density t) = 1 ∧
      (∀ t > 0, opExpression id (fun s => 2-s) opLinearProbe t = 2-t ∧
        opExpression id (fun s => 2-s) opQuadraticProbe t = t^2-6*t+6) ∧
      (∀ t > 0, HasDerivAt (fun s => s*SigmaPresentations.density s)
        ((2-t)*SigmaPresentations.density t) t) :=
  ⟨canonical_density_local_integral_ac, fun _ ht => SigmaPresentations.density_pos ht,
    intrinsic_density_integral_one, fun t _ => operator_canonical_probes t,
    fun t _ => operator_pearson_flux_derivative t⟩

end
end Sigma
