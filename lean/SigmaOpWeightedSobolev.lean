import SigmaOpWeightedLocal
import SigmaOpWeightedEnergy

namespace Sigma
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology ENNReal NNReal
open scoped ContDiff

/-- The usual finite disjoint-interval absolute-continuity condition on
every compact subinterval of the positive ray. -/
def PositiveRayLocallyAbsolutelyContinuous (H : ℝ → ℂ) : Prop :=
  ∀ l r : ℝ, 0 < l → ∀ ε : ℝ≥0∞, ε ≠ 0 →
    ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ (m : ℕ) (u v : Fin m → ℝ),
      (∀ i, l ≤ u i ∧ u i ≤ v i ∧ v i ≤ r) →
      Set.univ.PairwiseDisjoint (fun i => Ioc (u i) (v i)) →
      (∑ i, ENNReal.ofReal (v i-u i)) < δ →
      (∑ i, (‖H (v i)-H (u i)‖₊ : ℝ≥0∞)) < ε

theorem smooth_compact_gradient_local_derivative_tendsto
    (f : ℕ → ℝ → ℂ) (hf : ∀ k, ContDiff ℝ ∞ (f k))
    (hs : ∀ k, HasCompactSupport (f k)) (g : LaguerreWeightedHilbert)
    (hg : Tendsto (fun k => smoothCompactGradient (f k) (hf k) (hs k))
      atTop (𝓝 g)) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun k => ∫ t : ℝ in uIcc a b,
      ‖deriv (f k) t-weightedDerivativeRepresentative g t‖) atTop (𝓝 0) := by
  have hlim := gamma_l2_div_sqrt_local_L1_tendsto
    (fun k => smoothCompactGradient (f k) (hf k) (hs k)) g hg ha hb
  convert hlim using 1
  funext k
  apply integral_congr_ae
  have hcoe := gamma_ae_iff_positive_volume_ae.mp
    (smooth_compact_gradient_coe (f k) (hf k) (hs k))
  have hm : volume.restrict (uIcc a b) ≤ volume.restrict (Ioi 0) :=
    Measure.restrict_mono (fun t ht => (lt_min ha hb).trans_le ht.1) le_rfl
  filter_upwards [hm.absolutelyContinuous hcoe, ae_restrict_mem measurableSet_uIcc]
    with t ht htm
  have hp : 0 < t := (lt_min ha hb).trans_le htm.1
  have hsq : (Real.sqrt t : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hp).ne'
  rw [ht]
  simp only [weightedTestDerivative, weightedDerivativeRepresentative]
  rw [mul_div_cancel_left₀ _ hsq]

/-- Every vector in the actual square-root domain has a locally absolutely
continuous representative. Its literal derivative energy is finite and equals
the square-root operator energy; no regularity is imposed on the input vector. -/
theorem laguerre_square_root_regular_representative
    (x : (laguerreSpectralOperator Real.sqrt).domain) :
    ∃ H : ℝ → ℂ, H =ᵐ[gammaProbability] (x.val : ℝ → ℂ) ∧
      PositiveRayLocallyAbsolutelyContinuous H ∧
      IntegrableOn (fun t => steinFlux t*‖deriv H t‖^2) (Ioi 0) volume ∧
      (∫ t : ℝ in Ioi 0, steinFlux t*‖deriv H t‖^2) =
        ‖laguerreSpectralOperator Real.sqrt x‖^2 := by
  obtain ⟨f, hf, hs, _, g, _, hg, hfae, henergy⟩ :=
    laguerre_weighted_gradient_completion_ae x
  have hpos := operator_integer_samples_ae_pos gammaProbability
    operator_gamma_probability_integer_samples
  obtain ⟨H, hH, hder, hac⟩ := positive_sobolev_limit_regular_representative
    gammaProbability hpos f hf (x.val : ℝ → ℂ) (weightedDerivativeRepresentative g)
    (gamma_l2_div_sqrt_locally_integrable g) hfae
    (fun _ _ ha hb => smooth_compact_gradient_local_derivative_tendsto f hf hs g hg ha hb)
  obtain ⟨hi, he⟩ := regular_representative_weighted_energy g H hder
  exact ⟨H, hH, hac, hi, he.trans henergy⟩

theorem laguerre_square_root_derivative_energy
    (x : (laguerreSpectralOperator Real.sqrt).domain) :
    ∃ H : ℝ → ℂ, H =ᵐ[gammaProbability] (x.val : ℝ → ℂ) ∧
      PositiveRayLocallyAbsolutelyContinuous H ∧
      IntegrableOn (fun t => steinFlux t*‖deriv H t‖^2) (Ioi 0) volume ∧
      (∫ t : ℝ in Ioi 0, steinFlux t*‖deriv H t‖^2) =
        ∑' n : ℕ, (n : ℝ) * ‖laguerreCoefficient x.val n‖^2 := by
  obtain ⟨H, hH, hac, hi, he⟩ := laguerre_square_root_regular_representative x
  exact ⟨H, hH, hac, hi, he.trans (laguerre_square_root_energy x)⟩

end
end Sigma
