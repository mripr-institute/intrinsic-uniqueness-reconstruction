import SigmaCore

namespace Sigma
noncomputable section
open Filter Set
open scoped Topology

theorem unanchored_curvature_family (F : ℝ → ℝ)
    (hd : ∀ t > 0, DifferentiableAt ℝ F t)
    (hc : ∀ t > 0, HasDerivAt (deriv F) (-(1/t^2)) t) :
    ∀ t > 0, F t = H t + deriv F 1*(t-1)+F 1 := by
  have hq : ∀ t > 0, deriv F t = 1/t-1+deriv F 1 := by
    apply equal_of_equal_derivatives (deriv F) _
      (fun t ht => (hc t ht).differentiableAt)
      (fun t ht => ((reciprocal_hasDerivAt ht).add_const (deriv F 1)).differentiableAt)
    · intro t ht
      rw [(hc t ht).deriv, ((reciprocal_hasDerivAt ht).add_const (deriv F 1)).deriv]
    · simp
  have hg : ∀ t > 0, HasDerivAt (fun t => H t+deriv F 1*(t-1)+F 1)
      (1/t-1+deriv F 1) t := by
    intro t ht
    convert ((H_hasDerivAt ht).add
      (((hasDerivAt_id t).sub_const 1).const_mul (deriv F 1))).add_const (F 1) using 1
    ring
  apply equal_of_equal_derivatives F _ hd
    (fun t ht => (hg t ht).differentiableAt)
  · intro t ht
    rw [hq t ht, (hg t ht).deriv]
  · simp [H, SigmaPresentations.H]

theorem shifted_curvature_affine_family (F : ℝ → ℝ) (b : ℝ)
    (hd : ∀ r > b, DifferentiableAt ℝ F r)
    (hc : ∀ r > b, HasDerivAt (deriv F) (-(1/(r-b)^2)) r) :
    ∃ A B : ℝ, ∀ r > b, F r = Real.log (r-b)+A*r+B := by
  let G : ℝ → ℝ := fun t => F (t+b)
  have hG : ∀ t > 0, HasDerivAt G (deriv F (t+b)) t := by
    intro t ht
    have h := (hd (t+b) (by linarith)).hasDerivAt.comp t ((hasDerivAt_id t).add_const b)
    simpa [G] using h
  have hG2 : ∀ t > 0, HasDerivAt (deriv G) (-(1/t^2)) t := by
    intro t ht
    have h := (hc (t+b) (by linarith)).comp t ((hasDerivAt_id t).add_const b)
    have h' : HasDerivAt (fun t => deriv F (t+b)) (-(1/t^2)) t := by simpa using h
    apply h'.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
    exact (hG x hx).deriv
  have hf := unanchored_curvature_family G (fun t ht => (hG t ht).differentiableAt) hG2
  refine ⟨deriv G 1-1, F (1+b)+(1-deriv G 1)*(b+1), ?_⟩
  intro r hr
  have h := hf (r-b) (by linarith)
  dsimp [G, H, SigmaPresentations.H] at h ⊢
  simp only [sub_add_cancel] at h
  linarith

theorem affine_summand_two_data_unique (A B A' B' x y : ℝ)
    (hxy : x ≠ y) (hx : A*x+B = A'*x+B') (hy : A*y+B = A'*y+B') :
    A = A' ∧ B = B' := by
  have he : (A-A')*(x-y) = 0 := by nlinarith
  have hA : A = A' := sub_eq_zero.mp
    ((mul_eq_zero.mp he).resolve_right (sub_ne_zero.mpr hxy))
  exact ⟨hA, by rw [hA] at hx; linarith⟩

def shiftedLogAffine (b A B r : ℝ) : ℝ := Real.log (r-b)+A*r+B

theorem shiftedLogAffine_deriv (b A B r : ℝ) (hr : b < r) :
    HasDerivAt (shiftedLogAffine b A B) (1/(r-b)+A) r := by
  convert ((((hasDerivAt_id r).sub_const b).log (sub_ne_zero.mpr (ne_of_gt hr))).add
    ((hasDerivAt_id r).const_mul A)).add_const B using 1
  simp

theorem shiftedLogAffine_curvature (b A B r : ℝ) (hr : b < r) :
    HasDerivAt (deriv (shiftedLogAffine b A B)) (-(1/(r-b)^2)) r := by
  have hd := ((hasDerivAt_const r (1 : ℝ)).div
    ((hasDerivAt_id r).sub_const b) (sub_ne_zero.mpr (ne_of_gt hr))).add_const A
  have hd' : HasDerivAt (fun r => 1/(r-b)+A) (-(1/(r-b)^2)) r := by
    convert hd using 1
    simp [one_div, neg_div]
  apply hd'.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hr] with t ht
  exact (shiftedLogAffine_deriv b A B t ht).deriv

theorem one_affine_datum_insufficient (b A B x y : ℝ) (hxy : x ≠ y) :
    shiftedLogAffine b (A+1) (B-x) x = shiftedLogAffine b A B x ∧
    shiftedLogAffine b (A+1) (B-x) y ≠ shiftedLogAffine b A B y := by
  constructor
  · unfold shiftedLogAffine
    ring
  · intro h
    unfold shiftedLogAffine at h
    exact hxy (by nlinarith)

theorem intrinsic_equality_derivative (F : ℝ → ℝ)
    (he : ∀ t > 0, F t = H t) (t : ℝ) (ht : 0 < t) :
    HasDerivAt F (1/t-1) t := by
  apply (H_hasDerivAt ht).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
  exact he x hx

theorem intrinsic_equality_curvature (F : ℝ → ℝ)
    (he : ∀ t > 0, F t = H t) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (deriv F) (-(1/t^2)) t := by
  apply (reciprocal_hasDerivAt ht).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
  exact (intrinsic_equality_derivative F he x hx).deriv

theorem calibrated_curvature_iff (F : ℝ → ℝ)
    (hd : ∀ t > 0, DifferentiableAt ℝ F t) (hv : F 1 = 0) (hs : deriv F 1 = 0) :
    (∀ t > 0, HasDerivAt (deriv F) (-(1/t^2)) t) ↔ ∀ t > 0, F t = H t := by
  exact ⟨fun hc => curvature_reconstruction F hd hc hv hs, intrinsic_equality_curvature F⟩

theorem calibrated_riccati_iff (F : ℝ → ℝ)
    (hd : ∀ t > 0, DifferentiableAt ℝ F t) (hv : F 1 = 0) (hs : deriv F 1 = 0) :
    (∀ t > 0, HasDerivAt (deriv F) (-(deriv F t+1)^2) t) ↔
      ∀ t > 0, F t = H t := by
  refine ⟨fun hr => riccati_reconstruction F hd hr hv hs, ?_⟩
  intro he t ht
  have hd1 := (intrinsic_equality_derivative F he t ht).deriv
  have hd2 := intrinsic_equality_curvature F he t ht
  convert hd2 using 1
  rw [hd1]
  field_simp

end
end Sigma
