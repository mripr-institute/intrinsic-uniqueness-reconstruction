import SigmaProbSurvival

namespace Sigma
noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal

def deficitWeight (v : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-1 - v))

theorem deficit_weight_measurable : Measurable deficitWeight := by
  exact (continuous_const.sub continuous_id).rexp.measurable.ennreal_ofReal

theorem deficit_weight_ne_zero (v : ℝ) : deficitWeight v ≠ 0 := by
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))

theorem deficit_weight_ne_top (v : ℝ) : deficitWeight v ≠ ∞ := ENNReal.ofReal_ne_top

theorem map_with_linked_density (μ : Measure ℝ) (J : ℝ → ℝ) (hJ : Measurable J)
    (w : ℝ → ℝ≥0∞) (hw : Measurable w) :
    (Measure.map J μ).withDensity w = Measure.map J (μ.withDensity (w ∘ J)) := by
  ext s hs
  rw [withDensity_apply _ hs, Measure.map_apply hJ hs,
    withDensity_apply _ (hJ hs)]
  exact setLIntegral_map hs hw hJ

/-- Undoing the known strictly positive level weight recovers the full unweighted
pushforward measure. This is the Stieltjes-width step of P4, with actual measures. -/
theorem linked_deficit_law_recovers_level_measure (μ : Measure ℝ)
    (J K : ℝ → ℝ) (hJ : Measurable J) (hK : Measurable K)
    (hlaw : Measure.map J (μ.withDensity (deficitWeight ∘ J)) =
      Measure.map K (μ.withDensity (deficitWeight ∘ K))) :
    Measure.map J μ = Measure.map K μ := by
  rw [← map_with_linked_density μ J hJ deficitWeight deficit_weight_measurable,
    ← map_with_linked_density μ K hK deficitWeight deficit_weight_measurable] at hlaw
  have hu (ν : Measure ℝ) :
      (ν.withDensity deficitWeight).withDensity (fun x => (deficitWeight x)⁻¹) = ν :=
    withDensity_inv_same deficit_weight_measurable
      (Filter.Eventually.of_forall deficit_weight_ne_zero)
      (Filter.Eventually.of_forall deficit_weight_ne_top)
  have he := congrArg (fun ν : Measure ℝ =>
    ν.withDensity (fun x => (deficitWeight x)⁻¹)) hlaw
  simpa only [hu] using he

/-- Sublevel intervals turn equality of the recovered measures into numerical widths. -/
theorem linked_deficit_law_recovers_width (J K : ℝ → ℝ)
    (hJ : Measurable J) (hK : Measurable K)
    (hlaw : Measure.map J ((volume.restrict (Ioi 0)).withDensity (deficitWeight ∘ J)) =
      Measure.map K ((volume.restrict (Ioi 0)).withDensity (deficitWeight ∘ K)))
    (a b c d v : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hJI : J ⁻¹' Iic v ∩ Ioi 0 = Icc a b)
    (hKI : K ⁻¹' Iic v ∩ Ioi 0 = Icc c d) : b - a = d - c := by
  have he := linked_deficit_law_recovers_level_measure (volume.restrict (Ioi 0))
    J K hJ hK hlaw
  have hv := congrArg (fun ν : Measure ℝ => ν (Iic v)) he
  dsimp only at hv
  rw [Measure.map_apply hJ measurableSet_Iic, Measure.map_apply hK measurableSet_Iic,
    Measure.restrict_apply (hJ measurableSet_Iic),
    Measure.restrict_apply (hK measurableSet_Iic), hJI, hKI,
    Real.volume_Icc, Real.volume_Icc] at hv
  have hreal := congrArg ENNReal.toReal hv
  simpa only [ENNReal.toReal_ofReal (sub_nonneg.mpr hab),
    ENNReal.toReal_ofReal (sub_nonneg.mpr hcd)] using hreal

theorem coordinate_gap_strict_mono (j : ℝ → ℝ) (hj : StrictAntiOn j (Ici 1)) :
    StrictMonoOn (fun t => t - j t) (Ici 1) := by
  intro x hx y hy hxy
  have hh := hj hx hy hxy
  dsimp only
  linarith

/-- The coordinate involution and width determine the ordered root pair. -/
theorem linked_width_and_involution_determine_roots
    (j : ℝ → ℝ) (hj : StrictAntiOn j (Ici 1))
    (a b c d : ℝ) (hb : 1 ≤ b) (hd : 1 ≤ d)
    (ha : j b = a) (hc : j d = c) (hw : b - a = d - c) :
    a = c ∧ b = d := by
  have hgap : b - j b = d - j d := by rw [ha, hc]; exact hw
  have hbd : b = d := (coordinate_gap_strict_mono j hj).injOn hb hd hgap
  exact ⟨by rw [← ha, ← hc, hbd], hbd⟩

/-- Once paired branch inverses have been reconstructed, their potential is unique. -/
theorem paired_inverse_branches_identify_potential
    (J K a b : ℝ → ℝ)
    (haJ : ∀ v ≥ 0, J (a v) = v) (hbJ : ∀ v ≥ 0, J (b v) = v)
    (haK : ∀ v ≥ 0, K (a v) = v) (hbK : ∀ v ≥ 0, K (b v) = v)
    (hcover : ∀ t > 0, ∃ v ≥ 0, t = a v ∨ t = b v) :
    ∀ t > 0, J t = K t := by
  intro t ht
  obtain ⟨v, hv, ht⟩ := hcover t ht
  rcases ht with rfl | rfl
  · rw [haJ v hv, haK v hv]
  · rw [hbJ v hv, hbK v hv]

/-- The analytic candidate class of the linked deficit theorem. Values outside the
positive ray are used only to select a measurable extension. -/
structure TwoBranchPotential (J : ℝ → ℝ) : Prop where
  measurable : Measurable J
  continuous : ContinuousOn J (Ioi 0)
  anchor : J 1 = 0
  left_strict : StrictAntiOn J (Ioc 0 1)
  right_strict : StrictMonoOn J (Ici 1)
  left_limit : Tendsto J (𝓝[>] 0) atTop
  right_limit : Tendsto J atTop atTop

theorem TwoBranchPotential.nonnegative {J : ℝ → ℝ} (h : TwoBranchPotential J)
    {t : ℝ} (ht : 0 < t) : 0 ≤ J t := by
  rcases le_total t 1 with ht1 | h1t
  · have he := h.left_strict.antitoneOn (show t ∈ Ioc 0 1 from ⟨ht, ht1⟩)
      (show (1 : ℝ) ∈ Ioc 0 1 from ⟨by norm_num, le_rfl⟩) ht1
    simpa [h.anchor] using he
  · have he := h.right_strict.monotoneOn (show (1 : ℝ) ∈ Ici 1 by simp)
      h1t h1t
    simpa [h.anchor] using he

theorem TwoBranchPotential.roots {J : ℝ → ℝ} (h : TwoBranchPotential J)
    (v : ℝ) (hv : 0 ≤ v) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ 1 ∧ 1 ≤ b ∧ J a = v ∧ J b = v := by
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 1 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with t ht hlt
    exact ⟨ht, hlt⟩
  obtain ⟨l, hl, hlv⟩ := (hsmall.and ((tendsto_atTop.1 h.left_limit) v)).exists
  have hlc : ContinuousOn J (Icc l 1) := h.continuous.mono (by
    intro t ht
    exact lt_of_lt_of_le hl.1 ht.1)
  obtain ⟨a, ha, hav⟩ := intermediate_value_Icc' hl.2.le hlc
    (show v ∈ Icc (J 1) (J l) from ⟨by simpa [h.anchor] using hv, hlv⟩)
  obtain ⟨r, hr, hrv⟩ := ((eventually_ge_atTop (1 : ℝ)).and
    ((tendsto_atTop.1 h.right_limit) v)).exists
  have hrc : ContinuousOn J (Icc 1 r) := h.continuous.mono (by
    intro t ht
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ht.1)
  obtain ⟨b, hb, hbv⟩ := intermediate_value_Icc hr hrc
    (show v ∈ Icc (J 1) (J r) from ⟨by simpa [h.anchor] using hv, hrv⟩)
  exact ⟨a, b, lt_of_lt_of_le hl.1 ha.1, ha.2, hb.1, hav, hbv⟩

theorem TwoBranchPotential.sublevel_interval {J : ℝ → ℝ} (h : TwoBranchPotential J)
    (a b v : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1) (hb1 : 1 ≤ b)
    (ha : J a = v) (hb : J b = v) :
    J ⁻¹' Iic v ∩ Ioi 0 = Icc a b := by
  ext t
  constructor
  · rintro ⟨hjt, ht⟩
    change J t ≤ v at hjt
    change 0 < t at ht
    constructor
    · by_contra hta
      have hta' : t < a := lt_of_not_ge hta
      have he := h.left_strict ⟨ht, le_trans hta'.le ha1⟩ ⟨ha0, ha1⟩ hta'
      rw [ha] at he
      exact (not_lt_of_ge hjt) he
    · by_contra htb
      have hbt : b < t := lt_of_not_ge htb
      have he := h.right_strict hb1 (le_trans hb1 hbt.le) hbt
      rw [hb] at he
      exact (not_lt_of_ge hjt) he
  · intro ht
    refine ⟨?_, lt_of_lt_of_le ha0 ht.1⟩
    change J t ≤ v
    rcases le_total t 1 with ht1 | h1t
    · have he := h.left_strict.antitoneOn ⟨ha0, ha1⟩
        ⟨lt_of_lt_of_le ha0 ht.1, ht1⟩ ht.1
      simpa [ha] using he
    · have he := h.right_strict.monotoneOn h1t hb1 ht.2
      simpa [hb] using he

theorem TwoBranchPotential.pair_root {J : ℝ → ℝ} (h : TwoBranchPotential J)
    (j : ℝ → ℝ)
    (hpair : ∀ b ≥ 1, 0 < j b ∧ j b ≤ 1 ∧ J (j b) = J b)
    (a b v : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1) (hb1 : 1 ≤ b)
    (ha : J a = v) (hb : J b = v) : j b = a := by
  obtain ⟨hj0, hj1, hje⟩ := hpair b hb1
  apply h.left_strict.injOn ⟨hj0, hj1⟩ ⟨ha0, ha1⟩
  rw [hje, ha, hb]

/-- Complete linked-deficit uniqueness within the continuous strict-branch class.
This theorem uses actual pushforward laws under their linked densities. -/
theorem linked_deficit_and_involution_unique
    (J K : ℝ → ℝ) (hJ : TwoBranchPotential J) (hK : TwoBranchPotential K)
    (j : ℝ → ℝ) (hj : StrictAntiOn j (Ici 1))
    (hpairJ : ∀ b ≥ 1, 0 < j b ∧ j b ≤ 1 ∧ J (j b) = J b)
    (hpairK : ∀ b ≥ 1, 0 < j b ∧ j b ≤ 1 ∧ K (j b) = K b)
    (hlaw : Measure.map J ((volume.restrict (Ioi 0)).withDensity (deficitWeight ∘ J)) =
      Measure.map K ((volume.restrict (Ioi 0)).withDensity (deficitWeight ∘ K))) :
    ∀ t > 0, J t = K t := by
  have hbranches : ∀ v ≥ 0, ∃ a b : ℝ,
      0 < a ∧ a ≤ 1 ∧ 1 ≤ b ∧ J a = v ∧ J b = v ∧ K a = v ∧ K b = v := by
    intro v hv
    obtain ⟨a, b, ha0, ha1, hb1, ha, hb⟩ := hJ.roots v hv
    obtain ⟨c, d, hc0, hc1, hd1, hc, hd⟩ := hK.roots v hv
    have hw := linked_deficit_law_recovers_width J K hJ.measurable hK.measurable hlaw
      a b c d v (le_trans ha1 hb1) (le_trans hc1 hd1)
      (hJ.sublevel_interval a b v ha0 ha1 hb1 ha hb)
      (hK.sublevel_interval c d v hc0 hc1 hd1 hc hd)
    have hp := linked_width_and_involution_determine_roots j hj a b c d hb1 hd1
      (hJ.pair_root j hpairJ a b v ha0 ha1 hb1 ha hb)
      (hK.pair_root j hpairK c d v hc0 hc1 hd1 hc hd) hw
    exact ⟨a, b, ha0, ha1, hb1, ha, hb, hp.1.symm ▸ hc, hp.2.symm ▸ hd⟩
  intro t ht
  obtain ⟨a, b, ha0, ha1, hb1, ha, hb, hka, hkb⟩ :=
    hbranches (J t) (hJ.nonnegative ht)
  rcases le_total t 1 with ht1 | h1t
  · have hta : t = a := hJ.left_strict.injOn ⟨ht, ht1⟩ ⟨ha0, ha1⟩ ha.symm
    exact hka.symm.trans (congrArg K hta.symm)
  · have htb : t = b := hJ.right_strict.injOn h1t hb1 hb.symm
    exact hkb.symm.trans (congrArg K htb.symm)

theorem intrinsic_potential_two_branch : TwoBranchPotential SigmaBase.potential := by
  have hc : ContinuousOn SigmaBase.potential (Ioi 0) := by
    intro t ht
    exact (SigmaBase.potential_hasDerivAt ht).continuousAt.continuousWithinAt
  refine ⟨?_, hc, ?_, ?_, ?_, ?_, ?_⟩
  · exact (measurable_id.sub measurable_const).sub Real.measurable_log
  · simp [SigmaBase.potential]
  · apply strictAntiOn_of_deriv_neg (convex_Ioc 0 1) (hc.mono Ioc_subset_Ioi_self)
    intro x hx
    rw [interior_Ioc] at hx
    rw [(SigmaBase.potential_hasDerivAt hx.1).deriv]
    have hdiv : 1 < 1 / x := (one_lt_div hx.1).mpr hx.2
    linarith
  · apply strictMonoOn_of_deriv_pos (convex_Ici 1)
      (hc.mono (by intro t ht; exact lt_of_lt_of_le (by norm_num) ht))
    intro x hx
    rw [interior_Ici] at hx
    have hx0 : 0 < x := lt_trans (by norm_num) hx
    rw [(SigmaBase.potential_hasDerivAt hx0).deriv]
    have hdiv : 1 / x < 1 := (div_lt_one hx0).mpr hx
    linarith
  · apply tendsto_atTop.2
    intro b
    have hh := (tendsto_atBot.1 Real.tendsto_log_nhdsWithin_zero_right) (-(b + 1))
    filter_upwards [hh, self_mem_nhdsWithin] with t ht ht0
    change 0 < t at ht0
    unfold SigmaBase.potential
    linarith
  · apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (2 * (b + 1)), eventually_gt_atTop (0 : ℝ)]
      with t ht ht0
    have hl := Real.log_le_sub_one_of_pos (div_pos ht0 (by norm_num : (0:ℝ)<2))
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    rw [Real.log_div (ne_of_gt ht0) (by norm_num)] at hl
    unfold SigmaBase.potential
    linarith

/-- The canonical-target instance of the general linked uniqueness theorem.
The pairing premise says precisely that the observed coordinate map is the
canonical I-level pairing on the upper branch. -/
theorem canonical_linked_deficit_identifies_I
    (J : ℝ → ℝ) (hJ : TwoBranchPotential J)
    (j : ℝ → ℝ) (hj : StrictAntiOn j (Ici 1))
    (hpairJ : ∀ b ≥ 1, 0 < j b ∧ j b ≤ 1 ∧ J (j b) = J b)
    (hpairI : ∀ b ≥ 1, 0 < j b ∧ j b ≤ 1 ∧
      SigmaBase.potential (j b) = SigmaBase.potential b)
    (hlaw : Measure.map J ((volume.restrict (Ioi 0)).withDensity (deficitWeight ∘ J)) =
      Measure.map SigmaBase.potential ((volume.restrict (Ioi 0)).withDensity
        (deficitWeight ∘ SigmaBase.potential))) :
    ∀ t > 0, J t = SigmaBase.potential t :=
  linked_deficit_and_involution_unique J SigmaBase.potential hJ
    intrinsic_potential_two_branch j hj hpairJ hpairI hlaw

theorem TwoBranchPotential.pair_strictAnti {J : ℝ → ℝ} (hJ : TwoBranchPotential J)
    (j : ℝ → ℝ)
    (hpair : ∀ b ≥ 1, 0 < j b ∧ j b ≤ 1 ∧ J (j b) = J b) :
    StrictAntiOn j (Ici 1) := by
  intro b hb d hd hbd
  rcases hpair b hb with ⟨hb0, hb1, hbJ⟩
  rcases hpair d hd with ⟨hd0, hd1, hdJ⟩
  have he := hJ.right_strict hb hd hbd
  by_contra hh
  have hl := hJ.left_strict.antitoneOn ⟨hb0, hb1⟩ ⟨hd0, hd1⟩ (le_of_not_gt hh)
  rw [hbJ, hdJ] at hl
  exact (not_lt_of_ge hl) he

def positiveRayExtension (J : ℝ → ℝ) : ℝ → ℝ :=
  (Ioi (0 : ℝ)).piecewise J (fun _ => 0)

theorem positive_ray_extension_eq (J : ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    positiveRayExtension J t = J t := by simp [positiveRayExtension, ht]

/-- The manuscript's class needs regularity only on the positive ray. -/
structure RayPotential (J : ℝ → ℝ) : Prop where
  continuous : ContinuousOn J (Ioi 0)
  anchor : J 1 = 0
  left_strict : StrictAntiOn J (Ioc 0 1)
  right_strict : StrictMonoOn J (Ici 1)
  left_limit : Tendsto J (𝓝[>] 0) atTop
  right_limit : Tendsto J atTop atTop

theorem RayPotential.extension {J : ℝ → ℝ} (hJ : RayPotential J) :
    TwoBranchPotential (positiveRayExtension J) := by
  refine ⟨hJ.continuous.measurable_piecewise continuousOn_const measurableSet_Ioi,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply hJ.continuous.congr
    intro t ht
    exact positive_ray_extension_eq J ht
  · rw [positive_ray_extension_eq J (by norm_num : (0 : ℝ) < 1), hJ.anchor]
  · intro a ha b hb hab
    rw [positive_ray_extension_eq J ha.1, positive_ray_extension_eq J hb.1]
    exact hJ.left_strict ha hb hab
  · intro a ha b hb hab
    change 1 ≤ a at ha
    change 1 ≤ b at hb
    rw [positive_ray_extension_eq J (by linarith : 0 < a),
      positive_ray_extension_eq J (by linarith : 0 < b)]
    exact hJ.right_strict ha hb hab
  · apply hJ.left_limit.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (positive_ray_extension_eq J ht).symm
  · apply hJ.right_limit.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (positive_ray_extension_eq J ht).symm

/-- Literal positive-ray interface: neither global measurability nor a separate
monotonicity assumption on the supplied root pairing is needed. -/
theorem linked_deficit_and_involution_unique_on_positive_ray
    (J K : ℝ → ℝ) (hJ : RayPotential J) (hK : RayPotential K) (j : ℝ → ℝ)
    (hpairJ : ∀ b ≥ 1, 0 < j b ∧ j b ≤ 1 ∧ J (j b) = J b)
    (hpairK : ∀ b ≥ 1, 0 < j b ∧ j b ≤ 1 ∧ K (j b) = K b)
    (hlaw : Measure.map (positiveRayExtension J)
      ((volume.restrict (Ioi 0)).withDensity (deficitWeight ∘ positiveRayExtension J)) =
      Measure.map (positiveRayExtension K)
      ((volume.restrict (Ioi 0)).withDensity (deficitWeight ∘ positiveRayExtension K))) :
    ∀ t > 0, J t = K t := by
  have hpJ : ∀ b ≥ 1, 0 < j b ∧ j b ≤ 1 ∧
      positiveRayExtension J (j b) = positiveRayExtension J b := by
    intro b hb
    rcases hpairJ b hb with ⟨ha0, ha1, he⟩
    exact ⟨ha0, ha1, by rw [positive_ray_extension_eq J ha0,
      positive_ray_extension_eq J (by linarith : 0 < b), he]⟩
  have hpK : ∀ b ≥ 1, 0 < j b ∧ j b ≤ 1 ∧
      positiveRayExtension K (j b) = positiveRayExtension K b := by
    intro b hb
    rcases hpairK b hb with ⟨ha0, ha1, he⟩
    exact ⟨ha0, ha1, by rw [positive_ray_extension_eq K ha0,
      positive_ray_extension_eq K (by linarith : 0 < b), he]⟩
  have hu := linked_deficit_and_involution_unique _ _ hJ.extension hK.extension j
    (hJ.extension.pair_strictAnti j hpJ) hpJ hpK hlaw
  intro t ht
  simpa only [positive_ray_extension_eq J ht, positive_ray_extension_eq K ht] using hu t ht

end
end Sigma
