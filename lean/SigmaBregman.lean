import SigmaCore

namespace Sigma
noncomputable section
open Filter Set
open scoped Topology

def Bregman (F : ℝ → ℝ) (t s : ℝ) : ℝ :=
  F t-F s-deriv F s*(t-s)

def ScaleInvariantBregman (F : ℝ → ℝ) : Prop :=
  ∀ c > 0, ∀ t > 0, ∀ s > 0, Bregman F (c*t) (c*s) = Bregman F t s

def affinePotential (A B C : ℝ) (t : ℝ) : ℝ := A*I t+B*(t-1)+C

theorem affinePotential_derivative (A B C : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (affinePotential A B C) (A*(1-1/t)+B) t := by
  convert (((SigmaBase.potential_hasDerivAt ht).const_mul A).add
    (((hasDerivAt_id t).sub_const 1).const_mul B)).add_const C using 1
  ring

theorem bregman_scale_derivative (F : ℝ → ℝ)
    (hd : ∀ t > 0, DifferentiableAt ℝ F t)
    (hs : ScaleInvariantBregman F)
    (c t : ℝ) (hc : 0 < c) (ht : 0 < t) :
    c*(deriv F (c*t)-deriv F c) = deriv F t-deriv F 1 := by
  have hl := (((hd (c*t) (mul_pos hc ht)).hasDerivAt.comp t
    ((hasDerivAt_id t).const_mul c)).sub_const (F c)).sub
    ((((hasDerivAt_id t).const_mul c).sub_const c).const_mul (deriv F c))
  have hr := ((hd t ht).hasDerivAt.sub_const (F 1)).sub
    (((hasDerivAt_id t).sub_const 1).const_mul (deriv F 1))
  have he : HasDerivAt (fun t => F (c*t)-F c-deriv F c*(c*t-c))
      (deriv F t-deriv F 1*1) t := by
    apply hr.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
    simpa [Bregman] using hs c hc x hx 1 (by norm_num)
  have h := hl.unique he
  nlinarith

theorem bregman_scale_identifies_derivative (F : ℝ → ℝ)
    (hd : ∀ t > 0, DifferentiableAt ℝ F t)
    (hs : ScaleInvariantBregman F) (t : ℝ) (ht : 0 < t) :
    deriv F t = 2*(deriv F 2-deriv F 1)*(1-1/t)+deriv F 1 := by
  have h1 := bregman_scale_derivative F hd hs 2 t (by norm_num) ht
  have h2 := bregman_scale_derivative F hd hs t 2 ht (by norm_num)
  rw [mul_comm t 2] at h2
  field_simp
  nlinarith

theorem bregman_scale_classification (F : ℝ → ℝ)
    (hd : ∀ t > 0, DifferentiableAt ℝ F t)
    (hs : ScaleInvariantBregman F) :
    ∀ t > 0, F t = affinePotential (2*(deriv F 2-deriv F 1)) (deriv F 1) (F 1) t := by
  apply equal_of_equal_derivatives F _ hd
  · intro t ht
    exact (affinePotential_derivative _ _ _ ht).differentiableAt
  · intro t ht
    rw [(affinePotential_derivative _ _ _ ht).deriv]
    exact bregman_scale_identifies_derivative F hd hs t ht
  · simp [affinePotential, I, SigmaBase.potential]

theorem affinePotential_bregman (A B C : ℝ) {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    Bregman (affinePotential A B C) t s = A*I (t/s) := by
  unfold Bregman
  rw [(affinePotential_derivative A B C hs).deriv]
  have he := SigmaBase.normalized_bregman ht hs
  unfold affinePotential
  change A*I t+B*(t-1)+C-(A*I s+B*(s-1)+C)-(A*(1-1/s)+B)*(t-s) = A*I (t/s)
  calc
    _ = A*(I t-I s-(1-1/s)*(t-s)) := by ring
    _ = _ := congrArg (fun z => A*z) he

theorem affinePotential_scale (A B C : ℝ) :
    ScaleInvariantBregman (affinePotential A B C) := by
  intro c hc t ht s hs
  rw [affinePotential_bregman A B C (mul_pos hc ht) (mul_pos hc hs),
    affinePotential_bregman A B C ht hs, mul_div_mul_left t s (ne_of_gt hc)]

theorem calibrated_scale_bregman_unique (F : ℝ → ℝ)
    (hd : ∀ t > 0, DifferentiableAt ℝ F t)
    (hs : ScaleInvariantBregman F) (hv : F 1 = 0) (hd1 : deriv F 1 = 0)
    (hd2 : deriv F 2-deriv F 1 = 1/2) : ∀ t > 0, F t = I t := by
  intro t ht
  have h := bregman_scale_classification F hd hs t ht
  rw [hd2, hd1, hv] at h
  simpa [affinePotential] using h

theorem anchored_symmetric_bregman_unique (F : ℝ → ℝ)
    (hd : ∀ t > 0, DifferentiableAt ℝ F t)
    (hv : F 1 = 0) (hd1 : deriv F 1 = 0)
    (hs : ∀ t > 0, Bregman F t 1+Bregman F 1 t = t+1/t-2) :
    ∀ t > 0, F t = I t :=
  SigmaPresentations.reconstruct_anchored_symmetric_bregman F
    (fun t ht => (hd t ht).differentiableWithinAt) hv hd1 hs

theorem affinePotential_calibration (A B C : ℝ) :
    affinePotential A B C 1 = C ∧ deriv (affinePotential A B C) 1 = B ∧
    deriv (affinePotential A B C) 2-deriv (affinePotential A B C) 1 = A/2 := by
  rw [(affinePotential_derivative A B C (show (0 : ℝ) < 1 by norm_num)).deriv,
    (affinePotential_derivative A B C (show (0 : ℝ) < 2 by norm_num)).deriv]
  simp [affinePotential, I, SigmaBase.potential]
  ring

theorem affinePotential_parameters_unique (A B C A' B' C' : ℝ)
    (he : ∀ t > 0, affinePotential A B C t = affinePotential A' B' C' t) :
    A = A' ∧ B = B' ∧ C = C' := by
  have hd : ∀ t > 0, deriv (affinePotential A B C) t = deriv (affinePotential A' B' C') t := by
    intro t ht
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    exact he s hs
  have h1 := he 1 (by norm_num)
  have hd1 := hd 1 (by norm_num)
  have hd2 := congrArg (fun z => z-deriv (affinePotential A B C) 1) (hd 2 (by norm_num))
  rw [hd1] at hd2
  have h := affinePotential_calibration A B C
  have h' := affinePotential_calibration A' B' C'
  have hA : A = A' := by linarith [hd 2 (by norm_num)]
  exact ⟨hA, by linarith, by linarith⟩

theorem bregman_scale_iff_affine_family (F : ℝ → ℝ)
    (hd : ∀ t > 0, DifferentiableAt ℝ F t) :
    ScaleInvariantBregman F ↔ ∃ A B C : ℝ, ∀ t > 0, F t = affinePotential A B C t := by
  constructor
  · intro hs
    exact ⟨2*(deriv F 2-deriv F 1), deriv F 1, F 1, bregman_scale_classification F hd hs⟩
  · rintro ⟨A,B,C,he⟩ c hc t ht s hs
    have heD : ∀ x > 0, deriv F x = deriv (affinePotential A B C) x := by
      intro x hx
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
      exact he y hy
    change F (c*t)-F (c*s)-deriv F (c*s)*(c*t-c*s) = F t-F s-deriv F s*(t-s)
    rw [he (c*t) (mul_pos hc ht), he (c*s) (mul_pos hc hs), heD (c*s) (mul_pos hc hs),
      he t ht, he s hs, heD s hs]
    exact affinePotential_scale A B C c hc t ht s hs

/-- Varying each coordinate changes the function while the other two readouts are fixed. -/
theorem bregman_three_calibrations_independent :
    (¬ ∀ t > 0, affinePotential 2 0 0 t = affinePotential 1 0 0 t) ∧
    (¬ ∀ t > 0, affinePotential 1 1 0 t = affinePotential 1 0 0 t) ∧
    (¬ ∀ t > 0, affinePotential 1 0 1 t = affinePotential 1 0 0 t) := by
  constructor
  · intro h
    have he := affinePotential_parameters_unique 2 0 0 1 0 0 h
    norm_num at he
  · constructor
    · intro h
      have he := affinePotential_parameters_unique 1 1 0 1 0 0 h
      norm_num at he
    · intro h
      have he := affinePotential_parameters_unique 1 0 1 1 0 0 h
      norm_num at he

end
end Sigma
