import SigmaOpEndpointCutoff
import SigmaOpEndpointTransition

namespace Sigma
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

/-- The second zero-energy solution fails weighted L2 in every neighborhood
of zero; a hypothetical local L2 solution would give a maximal-domain cutoff
with constant nonzero endpoint flux, contradicting automatic zero flux. -/
theorem laguerre_second_zero_not_l2_at_zero (r : ℝ) (hr : 0 < r) :
    ¬Memℒp laguerreSecondZeroSolution 2 (gammaProbability.restrict (Ioo 0 r)) := by
  intro hi
  let a := r/2
  have ha : 0 < a := by dsimp [a]; linarith
  have har : a < r := by dsimp [a]; linarith
  let χ : ℝ → ℂ := fun t => 1-endpointTransition a r t
  have hχ : ContDiff ℝ ∞ χ := contDiff_const.sub (endpoint_transition_contDiff a r)
  have hχs : tsupport (deriv χ) ⊆ Icc a r := endpoint_transition_complement_derivative_support har
  have hs : HasCompactSupport (deriv χ) := isCompact_Icc.of_isClosed_subset isClosed_closure hχs
  have hp : tsupport (deriv χ) ⊆ Ioi 0 := fun t ht => ha.trans_le (hχs ht).1
  have hχU := gamma_local_l2_cutoff laguerreSecondZeroSolution χ measurableSet_Ioo hi hχ.continuous
    (endpoint_transition_complement_norm_le a r) (by
      intro t ht htr
      have hrt : r ≤ t := by by_contra hn; exact htr ⟨ht,lt_of_not_ge hn⟩
      dsimp only [χ]
      rw [endpoint_transition_one har hrt,sub_self])
  obtain ⟨x,hx⟩ := laguerre_zero_solution_cutoff_maximal χ hχ hs hp hχU
  have hlim := (laguerre_canonical_zero_flux x _ hx
    ((smooth_positive_locally_ac hχ).mul laguerre_second_zero_locally_ac)).1
  have he : (fun t => (steinFlux t : ℂ)*deriv (fun s => χ s*laguerreSecondZeroSolution s) t)
      =ᶠ[𝓝[>] (0:ℝ)] (fun _ => (1:ℂ)) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds] with t ht hta
    have hF : (fun s => χ s*laguerreSecondZeroSolution s) =ᶠ[𝓝 t] laguerreSecondZeroSolution := by
      filter_upwards [eventually_lt_nhds hta] with s hs
      dsimp only [χ]
      rw [endpoint_transition_zero har hs.le,sub_zero,one_mul]
    rw [hF.deriv_eq,laguerre_second_zero_flux ht]
  have hc : Tendsto (fun _ : ℝ => (1:ℂ)) (𝓝[>] (0:ℝ)) (𝓝 0) := hlim.congr' he
  have hz : (1:ℂ)=0 := tendsto_nhds_unique tendsto_const_nhds hc
  exact one_ne_zero hz

/-- The second solution also fails weighted L2 on every positive tail. -/
theorem laguerre_second_zero_not_l2_at_infinity (r : ℝ) (hr : 0 < r) :
    ¬Memℒp laguerreSecondZeroSolution 2 (gammaProbability.restrict (Ioi r)) := by
  intro hi
  let b := r+1
  have hrb : r < b := by dsimp [b]; linarith
  let χ := endpointTransition r b
  have hχ := endpoint_transition_contDiff r b
  have hχs : tsupport (deriv χ) ⊆ Icc r b := endpoint_transition_derivative_support hrb
  have hs : HasCompactSupport (deriv χ) := isCompact_Icc.of_isClosed_subset isClosed_closure hχs
  have hp : tsupport (deriv χ) ⊆ Ioi 0 := fun t ht => hr.trans_le (hχs ht).1
  have hχU := gamma_local_l2_cutoff laguerreSecondZeroSolution χ measurableSet_Ioi hi hχ.continuous
    (endpoint_transition_norm_le r b) (by
      intro t _ ht
      exact endpoint_transition_zero hrb (le_of_not_gt ht))
  obtain ⟨x,hx⟩ := laguerre_zero_solution_cutoff_maximal χ hχ hs hp hχU
  have hlim := (laguerre_canonical_zero_flux x _ hx
    ((smooth_positive_locally_ac hχ).mul laguerre_second_zero_locally_ac)).2
  have he : (fun t => (steinFlux t : ℂ)*deriv (fun s => χ s*laguerreSecondZeroSolution s) t)
      =ᶠ[atTop] (fun _ => (1:ℂ)) := by
    filter_upwards [eventually_gt_atTop b] with t ht
    have hF : (fun s => χ s*laguerreSecondZeroSolution s) =ᶠ[𝓝 t] laguerreSecondZeroSolution := by
      filter_upwards [eventually_gt_nhds ht] with s hs
      dsimp only [χ]
      rw [endpoint_transition_one hrb hs.le,one_mul]
    rw [hF.deriv_eq,laguerre_second_zero_flux (hr.trans (hrb.trans ht))]
  have hc : Tendsto (fun _ : ℝ => (1:ℂ)) atTop (𝓝 0) := hlim.congr' he
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hc)


/-- Actual locally regular solutions of the zero-energy Sturm--Liouville
expression. No Hilbert-space or endpoint assumption is included. -/
def LaguerreZeroEnergySolution (F : ℝ → ℂ) : Prop :=
  PositiveRayLocallyAbsolutelyContinuous F ∧
  PositiveRayLocallyAbsolutelyContinuous (fun t => (steinFlux t : ℂ)*deriv F t) ∧
  ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), laguerreDivergenceExpression F t=0

def LaguerreSquareIntegrableAtZero (F : ℝ → ℂ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ Memℒp F 2 (gammaProbability.restrict (Ioo 0 r))

def LaguerreSquareIntegrableAtInfinity (F : ℝ → ℂ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ Memℒp F 2 (gammaProbability.restrict (Ioi r))

/-- The Weyl classification at the fixed spectral parameter zero: an endpoint
is limit point precisely when not all zero-energy solutions are locally L2.
This is the single-parameter characterization used in the paper. No general
parameter-independence or abstract Weyl-alternative theorem is claimed here. -/
def LaguerreWeylLimitPoint (endpointL2 : (ℝ → ℂ) → Prop) : Prop :=
  ¬∀ F, LaguerreZeroEnergySolution F → endpointL2 F

theorem laguerre_second_zero_is_solution : LaguerreZeroEnergySolution laguerreSecondZeroSolution := by
  refine ⟨laguerre_second_zero_locally_ac,laguerre_second_zero_flux_locally_ac,?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact laguerre_second_zero_divergence ht


theorem laguerre_constant_zero_solution (c : ℂ) : LaguerreZeroEnergySolution (fun _ => c) := by
  have hd : deriv (fun _ : ℝ => c) = fun _ => 0 := funext fun t => deriv_const t c
  refine ⟨smooth_positive_locally_ac contDiff_const,?_,?_⟩
  · simpa only [hd,mul_zero] using
      (smooth_positive_locally_ac (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0:ℂ))))
  · filter_upwards with t
    simp only [laguerreDivergenceExpression,hd,mul_zero,deriv_const]

/-- Independence of the two zero-energy basis functions on the actual
positive ray. Together with the preceding spanning theorem this is a genuine
fundamental system. -/
theorem laguerre_zero_fundamental_independent (a b : ℂ)
    (he : EqOn (fun t => a+b*laguerreSecondZeroSolution t) (fun _ => 0) (Ioi 0)) :
    a=0 ∧ b=0 := by
  have hevent : (fun t => a+b*laguerreSecondZeroSolution t) =ᶠ[𝓝 (1:ℝ)] (fun _ => 0) := by
    filter_upwards [isOpen_Ioi.mem_nhds (by norm_num : (0:ℝ)<1)] with t ht
    exact he ht
  have hd := ((laguerre_second_zero_hasDerivAt (by norm_num : (0:ℝ)<1)).const_mul b).const_add a
  have hb : b=0 := by
    have hz := hevent.deriv_eq
    rw [hd.deriv,deriv_const] at hz
    exact (mul_eq_zero.mp hz).resolve_right (inv_ne_zero (stein_flux_ne_zero (by norm_num)))
  refine ⟨?_,hb⟩
  simpa only [hb,zero_mul,add_zero] using he (show (1:ℝ) ∈ Ioi 0 by norm_num)

private theorem zero_solution_l2_forces_constant (F : ℝ → ℂ)
    (hF : LaguerreZeroEnergySolution F) {S : Set ℝ} (hS : MeasurableSet S) (hp : S ⊆ Ioi 0)
    (hU : ¬Memℒp laguerreSecondZeroSolution 2 (gammaProbability.restrict S))
    (hi : Memℒp F 2 (gammaProbability.restrict S)) :
    ∃ a : ℂ, EqOn F (fun _ => a) (Ioi 0) := by
  obtain ⟨a,b,he⟩ := laguerre_zero_solution_fundamental_system F hF.1 hF.2.1 hF.2.2
  have hb : b=0 := by
    by_contra hb
    apply hU
    have hm := (hi.sub (memℒp_const a)).const_mul b⁻¹
    apply hm.ae_eq
    filter_upwards [ae_restrict_mem hS] with t ht
    change b⁻¹*(F t-a)=laguerreSecondZeroSolution t
    rw [he (hp ht)]
    field_simp
  exact ⟨a,fun t ht => by simpa only [hb,zero_mul,add_zero] using he ht⟩

theorem laguerre_zero_solution_l2_at_zero_iff_constant (F : ℝ → ℂ)
    (hF : LaguerreZeroEnergySolution F) :
    LaguerreSquareIntegrableAtZero F ↔ ∃ a : ℂ, EqOn F (fun _ => a) (Ioi 0) := by
  constructor
  · rintro ⟨r,hr,hi⟩
    exact zero_solution_l2_forces_constant F hF measurableSet_Ioo Ioo_subset_Ioi_self
      (laguerre_second_zero_not_l2_at_zero r hr) hi
  · rintro ⟨a,ha⟩
    refine ⟨1,by norm_num,(memℒp_const a).ae_eq ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (ha ht.1).symm

theorem laguerre_zero_solution_l2_at_infinity_iff_constant (F : ℝ → ℂ)
    (hF : LaguerreZeroEnergySolution F) :
    LaguerreSquareIntegrableAtInfinity F ↔ ∃ a : ℂ, EqOn F (fun _ => a) (Ioi 0) := by
  constructor
  · rintro ⟨r,hr,hi⟩
    exact zero_solution_l2_forces_constant F hF measurableSet_Ioi (fun _ ht => hr.trans ht)
      (laguerre_second_zero_not_l2_at_infinity r hr) hi
  · rintro ⟨a,ha⟩
    refine ⟨1,by norm_num,(memℒp_const a).ae_eq ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (ha (lt_trans zero_lt_one ht)).symm

/-- Both singular endpoints are limit point in the paper's zero-energy Weyl
classification, with precisely the constant locally L2 solution direction. -/
theorem laguerre_both_endpoints_limit_point :
    LaguerreWeylLimitPoint LaguerreSquareIntegrableAtZero ∧
      LaguerreWeylLimitPoint LaguerreSquareIntegrableAtInfinity := by
  constructor
  · intro h
    obtain ⟨r,hr,hi⟩ := h laguerreSecondZeroSolution laguerre_second_zero_is_solution
    exact laguerre_second_zero_not_l2_at_zero r hr hi
  · intro h
    obtain ⟨r,hr,hi⟩ := h laguerreSecondZeroSolution laguerre_second_zero_is_solution
    exact laguerre_second_zero_not_l2_at_infinity r hr hi

end
end Sigma
