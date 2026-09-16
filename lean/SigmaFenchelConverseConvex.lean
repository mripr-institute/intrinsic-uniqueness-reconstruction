import SigmaFenchelConverseLSC

namespace Sigma
noncomputable section
open Set Filter
open scoped Topology

/-- Convexity of the native real epigraph forces finiteness between nearby finite contacts. -/
theorem fenchel_convex_candidate_finite (F : ℝ → EReal)
    (hc : fullFenchelConjugate F = intrinsicConjugateTarget)
    (hv : ExtendedConvex F) {t₀ : ℝ} (ht₀ : 0 < t₀) : F t₀ ≠ ⊤ := by
  obtain ⟨x, r, hx, hxd, hxr, _⟩ := fenchel_candidate_local_contact F hc
    (show 0 < t₀/2 by linarith) (show 0 < t₀/4 by linarith) (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨y, s, hy, hyd, hys, _⟩ := fenchel_candidate_local_contact F hc
    (show 0 < t₀+1 by linarith) (show (0 : ℝ) < 1/2 by norm_num) (show (0 : ℝ) < 1 by norm_num)
  have hxt : x < t₀ := by have hh := (abs_lt.mp hxd).2; linarith
  have hty : t₀ < y := by have hh := (abs_lt.mp hyd).1; linarith
  have hxy : 0 < y-x := by linarith
  let a := (y-t₀)/(y-x)
  let b := (t₀-x)/(y-x)
  have ha : 0 ≤ a := (div_pos (sub_pos.mpr hty) hxy).le
  have hb : 0 ≤ b := (div_pos (sub_pos.mpr hxt) hxy).le
  have hab : a+b=1 := by dsimp [a,b]; field_simp
  have hsum : a*x+b*y=t₀ := by dsimp [a,b]; field_simp; ring
  have hp : F (a*x+b*y) ≤ ((a*r+b*s : ℝ) : EReal) :=
    hv (show (x,r) ∈ {p : ℝ × ℝ | F p.1 ≤ (p.2 : EReal)} by simpa [hxr])
      (show (y,s) ∈ {p : ℝ × ℝ | F p.1 ≤ (p.2 : EReal)} by simpa [hys]) ha hb hab
  rw [hsum] at hp
  exact ne_of_lt (lt_of_le_of_lt hp (EReal.coe_lt_top _))

theorem fenchel_convex_candidate_real_convex (F : ℝ → EReal)
    (hc : fullFenchelConjugate F = intrinsicConjugateTarget)
    (hv : ExtendedConvex F) : ConvexOn ℝ (Ioi 0) (fun t => (F t).toReal) := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have hf (t : ℝ) (ht : 0 < t) : ((F t).toReal : EReal) = F t :=
    EReal.coe_toReal (fenchel_convex_candidate_finite F hc hv ht) (fenchel_candidate_ne_bot F hc t)
  have hp := hv (show (x,(F x).toReal) ∈ {p : ℝ × ℝ | F p.1 ≤ (p.2 : EReal)} by change F x ≤ ((F x).toReal : EReal); rw [hf x hx])
    (show (y,(F y).toReal) ∈ {p : ℝ × ℝ | F p.1 ≤ (p.2 : EReal)} by change F y ≤ ((F y).toReal : EReal); rw [hf y hy]) ha hb hab
  have hz : 0 < a*x+b*y := (convex_Ioi (0 : ℝ)) hx hy ha hb hab
  change F (a*x+b*y) ≤ ((a*(F x).toReal+b*(F y).toReal : ℝ) : EReal) at hp
  rw [← hf _ hz, EReal.coe_le_coe_iff] at hp
  exact hp

/-- Native epigraph convexity interpolates a common finite upper height. -/
theorem extended_convex_bracket_bound (F : ℝ → EReal) (hv : ExtendedConvex F)
    {x t y B : ℝ} (hxt : x < t) (hty : t < y)
    (hx : F x ≤ (B : EReal)) (hy : F y ≤ (B : EReal)) : F t ≤ (B : EReal) := by
  have hxy : 0 < y-x := by linarith
  let a := (y-t)/(y-x)
  let b := (t-x)/(y-x)
  have ha : 0 ≤ a := (div_pos (sub_pos.mpr hty) hxy).le
  have hb : 0 ≤ b := (div_pos (sub_pos.mpr hxt) hxy).le
  have hab : a+b=1 := by dsimp [a,b]; field_simp
  have hsum : a*x+b*y=t := by dsimp [a,b]; field_simp; ring
  have hp := hv (show (x,B) ∈ {p : ℝ × ℝ | F p.1 ≤ (p.2 : EReal)} from hx)
    (show (y,B) ∈ {p : ℝ × ℝ | F p.1 ≤ (p.2 : EReal)} from hy) ha hb hab
  change F (a*x+b*y) ≤ ((a*B+b*B : ℝ) : EReal) at hp
  rwa [hsum, ← add_mul, hab, one_mul] at hp

/-- The convex branch uses finite contacts on both sides and native epigraph convexity.
It does not assume lower semicontinuity or invoke biconjugation. -/
theorem fenchel_convex_identifies (F : ℝ → EReal)
    (hc : fullFenchelConjugate F = intrinsicConjugateTarget)
    (hv : ExtendedConvex F) : F = extendedIntrinsic := by
  funext t₀
  by_cases ht₀ : 0 < t₀
  · apply le_antisymm
    · by_contra hn
      have hg : (I t₀ : EReal) < F t₀ := by
        simpa only [extendedIntrinsic, if_pos ht₀] using lt_of_not_ge hn
      obtain ⟨B, hIB, hBF⟩ := EReal.exists_between_coe_real hg
      have hε : 0 < (B-I t₀)/2 := by
        have hh := EReal.coe_lt_coe_iff.mp hIB
        linarith
      obtain ⟨δ,hδ,hcontrol⟩ := Metric.continuousAt_iff.mp
        (SigmaBase.potential_hasDerivAt ht₀).continuousAt ((B-I t₀)/2) hε
      let d := min δ t₀
      have hd : 0 < d := lt_min hδ ht₀
      have hdδ : d ≤ δ := min_le_left _ _
      have hdt : d ≤ t₀ := min_le_right _ _
      have hleft : 0 < t₀-d/2 := by linarith
      have hright : 0 < t₀+d/2 := by linarith
      have hIl : I (t₀-d/2) < I t₀+(B-I t₀)/2 := by
        have hh := hcontrol (show dist (t₀-d/2) t₀ < δ by
          rw [Real.dist_eq, show t₀-d/2-t₀ = -(d/2) by ring, abs_neg, abs_of_pos (by linarith)]
          linarith)
        rw [Real.dist_eq] at hh
        have hh' := (abs_lt.mp hh).2
        linarith
      have hIr : I (t₀+d/2) < I t₀+(B-I t₀)/2 := by
        have hh := hcontrol (show dist (t₀+d/2) t₀ < δ by
          rw [Real.dist_eq, show t₀+d/2-t₀ = d/2 by ring, abs_of_pos (by linarith)]
          linarith)
        rw [Real.dist_eq] at hh
        have hh' := (abs_lt.mp hh).2
        linarith
      obtain ⟨x,r,hx,hxd,hxr,hr⟩ := fenchel_candidate_local_contact F hc hleft
        (show 0 < d/4 by linarith) hε
      obtain ⟨y,s,hy,hyd,hys,hs⟩ := fenchel_candidate_local_contact F hc hright
        (show 0 < d/4 by linarith) hε
      have hxt : x < t₀ := by have hh := (abs_lt.mp hxd).2; linarith
      have hty : t₀ < y := by have hh := (abs_lt.mp hyd).1; linarith
      have hxB : F x ≤ (B : EReal) := by rw [hxr, EReal.coe_le_coe_iff]; linarith
      have hyB : F y ≤ (B : EReal) := by rw [hys, EReal.coe_le_coe_iff]; linarith
      exact (not_le_of_gt hBF) (extended_convex_bracket_bound F hv hxt hty hxB hyB)
    · exact fenchel_candidate_lower_bound F hc t₀
  · rw [fenchel_candidate_off_positive F hc (le_of_not_gt ht₀)]
    simp [extendedIntrinsic, ht₀]

theorem fenchel_convex_candidate_lower_semicontinuous (F : ℝ → EReal)
    (hc : fullFenchelConjugate F = intrinsicConjugateTarget)
    (hv : ExtendedConvex F) : LowerSemicontinuousOn F (Ioi 0) := by
  rw [fenchel_convex_identifies F hc hv]
  exact extended_intrinsic_lower_semicontinuousOn

/-- Exact final:C5 inverse with either of the stated regularity conditions. -/
theorem exact_legendre_target_identifies (F : ℝ → EReal)
    (hc : fullFenchelConjugate F = intrinsicConjugateTarget)
    (hr : LowerSemicontinuousOn F (Ioi 0) ∨ ExtendedConvex F) : F = extendedIntrinsic := by
  rcases hr with hl | hv
  · exact fenchel_lower_semicontinuous_identifies F hc hl
  · exact fenchel_convex_identifies F hc hv

end
end Sigma
