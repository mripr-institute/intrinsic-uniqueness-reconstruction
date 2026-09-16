import SigmaProbCanonicalPair

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

/-- The part of the two real Lambert branches used in the manuscript.  Every
observed argument is in this interval; zero is excluded for the lower branch. -/
def NegativeLambertDomain (z : ℝ) : Prop := -Real.exp (-1) ≤ z ∧ z < 0

def PrincipalNegativeLambertRoot (z w : ℝ) : Prop :=
  -1 ≤ w ∧ w < 0 ∧ w*Real.exp w = z

def LowerNegativeLambertRoot (z w : ℝ) : Prop :=
  w ≤ -1 ∧ w*Real.exp w = z

theorem intrinsic_real_density_value (t : ℝ) (ht : 0 < t) :
    SigmaPresentations.density t = Real.exp (-1-SigmaBase.potential t) := by
  unfold SigmaPresentations.density SigmaBase.potential
  have he : -1-(t-1-Real.log t) = Real.log t+(-t) := by ring
  rw [he,Real.exp_add,Real.exp_log ht]

theorem negative_lambert_root_from_potential (t v : ℝ) (ht : 0 < t)
    (hv : SigmaBase.potential t = v) :
    (-t)*Real.exp (-t) = -Real.exp (-1-v) := by
  have hh := intrinsic_real_density_value t ht
  rw [hv] at hh
  simpa only [SigmaPresentations.density, neg_mul] using congrArg Neg.neg hh

theorem negative_lambert_level_nonnegative (z : ℝ) (hz : NegativeLambertDomain z) :
    0 ≤ -1-Real.log (-z) := by
  have hp : 0 < -z := neg_pos.mpr hz.2
  have he : Real.log (-z) ≤ -1 :=
    (Real.log_le_iff_le_exp hp).mpr (by linarith [hz.1])
  linarith

theorem negative_lambert_argument_level (z : ℝ) (hz : z < 0) :
    -Real.exp (-1-(-1-Real.log (-z))) = z := by
  have he : -1-(-1-Real.log (-z)) = Real.log (-z) := by ring
  rw [he,Real.exp_log (neg_pos.mpr hz),neg_neg]

theorem negative_lambert_roots_exist (z : ℝ) (hz : NegativeLambertDomain z) :
    (∃ w, PrincipalNegativeLambertRoot z w) ∧ (∃ w, LowerNegativeLambertRoot z w) := by
  let v := -1-Real.log (-z)
  have hv : 0 ≤ v := negative_lambert_level_nonnegative z hz
  have hs := canonical_deficit_roots_spec v hv
  have ha := negative_lambert_root_from_potential _ v hs.1 hs.2.2.2.1
  have hb := negative_lambert_root_from_potential _ v (by linarith [hs.2.2.1]) hs.2.2.2.2
  rw [show -Real.exp (-1-v) = z from negative_lambert_argument_level z hz.2] at ha hb
  exact ⟨⟨-(canonicalDeficitRoots v).1,by unfold PrincipalNegativeLambertRoot; exact
    ⟨by linarith [hs.2.1],neg_neg_of_pos hs.1,ha⟩⟩,
    ⟨-(canonicalDeficitRoots v).2,by unfold LowerNegativeLambertRoot; exact
    ⟨by linarith [hs.2.2.1],hb⟩⟩⟩

theorem negative_lambert_root_potential (z w : ℝ) (hw : w < 0)
    (he : w*Real.exp w = z) : SigmaBase.potential (-w) = -1-Real.log (-z) := by
  have he2 : (-w)*Real.exp (-(-w)) = -z := by
    rw [neg_neg,neg_mul,he]
  have hh := congrArg Real.log he2
  rw [Real.log_mul (neg_pos.mpr hw).ne' (Real.exp_ne_zero _),Real.log_exp] at hh
  unfold SigmaBase.potential
  linarith

theorem principal_negative_lambert_root_unique (z w u : ℝ)
    (hw : PrincipalNegativeLambertRoot z w) (hu : PrincipalNegativeLambertRoot z u) : w = u := by
  have hpw := negative_lambert_root_potential z w hw.2.1 hw.2.2
  have hpu := negative_lambert_root_potential z u hu.2.1 hu.2.2
  have he := intrinsic_potential_two_branch.left_strict.injOn
    (show -w ∈ Ioc (0 : ℝ) 1 from ⟨by linarith [hw.2.1],by linarith [hw.1]⟩)
    (show -u ∈ Ioc (0 : ℝ) 1 from ⟨by linarith [hu.2.1],by linarith [hu.1]⟩)
    (hpw.trans hpu.symm)
  linarith

theorem lower_negative_lambert_root_unique (z w u : ℝ)
    (hw : LowerNegativeLambertRoot z w) (hu : LowerNegativeLambertRoot z u) : w = u := by
  have hpw := negative_lambert_root_potential z w (by linarith [hw.1]) hw.2
  have hpu := negative_lambert_root_potential z u (by linarith [hu.1]) hu.2
  have he := intrinsic_potential_two_branch.right_strict.injOn
    (show -w ∈ Ici (1 : ℝ) by change 1 ≤ -w; linarith [hw.1])
    (show -u ∈ Ici (1 : ℝ) by change 1 ≤ -u; linarith [hu.1])
    (hpw.trans hpu.symm)
  linarith

def negativeLambertW0 (z : ℝ) : ℝ := by
  classical
  exact if hz : NegativeLambertDomain z then Classical.choose (negative_lambert_roots_exist z hz).1 else 0

def negativeLambertWm1 (z : ℝ) : ℝ := by
  classical
  exact if hz : NegativeLambertDomain z then Classical.choose (negative_lambert_roots_exist z hz).2 else 0

theorem negative_lambert_W0_spec (z : ℝ) (hz : NegativeLambertDomain z) :
    PrincipalNegativeLambertRoot z (negativeLambertW0 z) := by
  simp only [negativeLambertW0,dif_pos hz]
  exact Classical.choose_spec (negative_lambert_roots_exist z hz).1

theorem negative_lambert_Wm1_spec (z : ℝ) (hz : NegativeLambertDomain z) :
    LowerNegativeLambertRoot z (negativeLambertWm1 z) := by
  simp only [negativeLambertWm1,dif_pos hz]
  exact Classical.choose_spec (negative_lambert_roots_exist z hz).2

theorem deficit_lambert_argument_domain (v : ℝ) (hv : 0 ≤ v) :
    NegativeLambertDomain (-Real.exp (-1-v)) := by
  constructor
  · have hh : Real.exp (-1-v) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    linarith
  · exact neg_neg_of_pos (Real.exp_pos _)

theorem canonical_deficit_roots_lambert (v : ℝ) (hv : 0 ≤ v) :
    (canonicalDeficitRoots v).1 = -negativeLambertW0 (-Real.exp (-1-v)) ∧
    (canonicalDeficitRoots v).2 = -negativeLambertWm1 (-Real.exp (-1-v)) := by
  have hs := canonical_deficit_roots_spec v hv
  have hz := deficit_lambert_argument_domain v hv
  have ha := negative_lambert_root_from_potential _ v hs.1 hs.2.2.2.1
  have hb := negative_lambert_root_from_potential _ v (by linarith [hs.2.2.1]) hs.2.2.2.2
  have hwa : PrincipalNegativeLambertRoot (-Real.exp (-1-v)) (-(canonicalDeficitRoots v).1) :=
    ⟨by linarith [hs.2.1],neg_neg_of_pos hs.1,ha⟩
  have hwb : LowerNegativeLambertRoot (-Real.exp (-1-v)) (-(canonicalDeficitRoots v).2) :=
    ⟨by linarith [hs.2.2.1],hb⟩
  have h0 := principal_negative_lambert_root_unique _ _ _ hwa (negative_lambert_W0_spec _ hz)
  have hm := lower_negative_lambert_root_unique _ _ _ hwb (negative_lambert_Wm1_spec _ hz)
  exact ⟨by linarith,by linarith⟩

theorem gamma_deficit_cdf_lambert (v : ℝ) (hv : 0 ≤ v) :
    gammaDeficitProbability (Iic v) = ENNReal.ofReal
      (gammaSurvival (-negativeLambertW0 (-Real.exp (-1-v)))-
        gammaSurvival (-negativeLambertWm1 (-Real.exp (-1-v)))) := by
  rw [canonical_deficit_cdf v hv,(canonical_deficit_roots_lambert v hv).1,
    (canonical_deficit_roots_lambert v hv).2]

theorem canonical_deficit_involution_lambert_lower (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    canonicalDeficitInvolution t = -negativeLambertWm1 (-(t*Real.exp (-t))) := by
  rw [canonicalDeficitInvolution,if_pos ht,if_pos ht1,
    (canonical_deficit_roots_lambert _ (intrinsic_potential_two_branch.nonnegative ht)).2]
  rw [← intrinsic_real_density_value t ht]
  rfl

theorem canonical_deficit_involution_lambert_upper (t : ℝ) (ht : 1 < t) :
    canonicalDeficitInvolution t = -negativeLambertW0 (-(t*Real.exp (-t))) := by
  have ht0 : 0 < t := by linarith
  rw [canonicalDeficitInvolution,if_pos ht0,if_neg (not_lt_of_ge ht.le),
    (canonical_deficit_roots_lambert _ (intrinsic_potential_two_branch.nonnegative ht0)).1]
  rw [← intrinsic_real_density_value t ht0]
  rfl

end
end Sigma
