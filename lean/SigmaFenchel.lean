import SigmaCore

namespace Sigma
noncomputable section
open Set

theorem intrinsic_deficit_nonnegative {t : ℝ} (ht : 0 < t) : 0 ≤ I t := by
  have h := Real.log_le_sub_one_of_pos ht
  unfold I SigmaBase.potential
  linarith

theorem intrinsic_deficit_zero_iff {t : ℝ} (ht : 0 < t) : I t = 0 ↔ t = 1 := by
  constructor
  · intro h
    by_contra he
    have hlog := Real.log_lt_sub_one_of_pos ht he
    unfold I SigmaBase.potential at h
    linarith
  · intro h
    simp [h, I, SigmaBase.potential]

theorem fenchel_deficit_identity {θ t : ℝ} (hθ : θ < 1) (ht : 0 < t) :
    θ*t-I t+Real.log (1-θ) = -I ((1-θ)*t) := by
  unfold I SigmaBase.potential
  rw [Real.log_mul (by linarith : 1-θ ≠ 0) (ne_of_gt ht)]
  ring

theorem fenchel_upper_bound {θ t : ℝ} (hθ : θ < 1) (ht : 0 < t) :
    θ*t-I t ≤ -Real.log (1-θ) := by
  have hd := intrinsic_deficit_nonnegative (mul_pos (sub_pos.mpr hθ) ht)
  have he := fenchel_deficit_identity hθ ht
  linarith

theorem fenchel_equality_iff {θ t : ℝ} (hθ : θ < 1) (ht : 0 < t) :
    θ*t-I t = -Real.log (1-θ) ↔ t = 1/(1-θ) := by
  have hpos : 0 < 1-θ := sub_pos.mpr hθ
  have he := fenchel_deficit_identity hθ ht
  constructor
  · intro h
    have hz : I ((1-θ)*t) = 0 := by linarith
    have hval := (intrinsic_deficit_zero_iff (mul_pos hpos ht)).mp hz
    apply (eq_div_iff (ne_of_gt hpos)).mpr
    nlinarith
  · intro h
    have hval : (1-θ)*t = 1 := by rw [h]; field_simp
    rw [hval] at he
    norm_num [I, SigmaBase.potential] at he
    unfold I SigmaBase.potential
    linarith

def fenchelValues (θ : ℝ) : Set ℝ := {v | ∃ t > 0, v = θ*t-I t}

theorem intrinsic_conjugate_greatest {θ : ℝ} (hθ : θ < 1) :
    IsGreatest (fenchelValues θ) (-Real.log (1-θ)) := by
  have hp : 0 < 1/(1-θ) := one_div_pos.mpr (sub_pos.mpr hθ)
  constructor
  · exact ⟨1/(1-θ), hp, ((fenchel_equality_iff hθ hp).mpr rfl).symm⟩
  · rintro y ⟨t,ht,rfl⟩
    exact fenchel_upper_bound hθ ht

theorem intrinsic_conjugate_unbounded {θ : ℝ} (hθ : 1 ≤ θ) :
    ¬ BddAbove (fenchelValues θ) := by
  rintro ⟨M,hM⟩
  have hm := hM (show θ*Real.exp M-I (Real.exp M) ∈ fenchelValues θ from
    ⟨Real.exp M, Real.exp_pos M, rfl⟩)
  have hn : 0 ≤ (θ-1)*Real.exp M := mul_nonneg (sub_nonneg.mpr hθ) (Real.exp_pos M).le
  unfold I SigmaBase.potential at hm
  rw [Real.log_exp] at hm
  nlinarith

end
end Sigma
