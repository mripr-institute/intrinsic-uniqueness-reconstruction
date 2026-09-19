import SigmaRealSpatial
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Sigma
noncomputable section
open Set Filter
open scoped Topology InnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The Euclidean Laplacian is the sum of actual second directional
derivatives along an orthonormal basis. -/
def euclideanLaplacian {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (g : V → ℝ) (x : V) : ℝ :=
  ∑ i, deriv (deriv (fun t : ℝ => g (x+t • b i))) 0

theorem norm_line_hasDerivAt (x u : V) (t : ℝ) (ht : x+t • u ≠ 0) :
    HasDerivAt (fun s : ℝ => ‖x+s • u‖) (⟪x+t • u,u⟫_ℝ/‖x+t • u‖) t := by
  have hl : HasDerivAt (fun s : ℝ => x+s • u) u t := by
    simpa using (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const u)
  have hn : ‖x+t • u‖ ≠ 0 := norm_ne_zero_iff.mpr ht
  convert hl.norm_sq.sqrt (pow_ne_zero 2 hn) using 1
  · funext s
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  · rw [Real.sqrt_sq (norm_nonneg _)]
    field_simp
    ring

theorem radial_direction_second_derivative (f : ℝ → ℝ)
    (hf : DifferentiableOn ℝ f (Ioi 0)) (x u : V) (hx : x ≠ 0)
    (hf₂ : DifferentiableAt ℝ (deriv f) ‖x‖) :
    deriv (deriv (fun t : ℝ => f ‖x+t • u‖)) 0 =
      deriv (deriv f) ‖x‖*⟪x,u⟫_ℝ^2/‖x‖^2+
      deriv f ‖x‖*(‖u‖^2/‖x‖-⟪x,u⟫_ℝ^2/‖x‖^3) := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hnorm : HasDerivAt (fun t : ℝ => ‖x+t • u‖) (⟪x,u⟫_ℝ/‖x‖) 0 := by
    simpa using norm_line_hasDerivAt x u 0 (by simpa using hx)
  have hinner : HasDerivAt (fun t : ℝ => ⟪x+t • u,u⟫_ℝ) (‖u‖^2) 0 := by
    have hl : HasDerivAt (fun s : ℝ => x+s • u) u 0 := by
      simpa using (hasDerivAt_const 0 x).add ((hasDerivAt_id (0:ℝ)).smul_const u)
    simpa [real_inner_self_eq_norm_sq] using hl.inner ℝ (hasDerivAt_const 0 u)
  have hcomp : HasDerivAt (fun t : ℝ => deriv f ‖x+t • u‖)
      (deriv (deriv f) ‖x‖*(⟪x,u⟫_ℝ/‖x‖)) 0 := by
    have hf₂' : HasDerivAt (deriv f) (deriv (deriv f) ‖x‖) ‖x+(0:ℝ) • u‖ := by
      simpa using hf₂.hasDerivAt
    exact hf₂'.comp 0 hnorm
  have hd := hcomp.mul (hinner.div hnorm (by simpa using hn.ne'))
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, x+t • u ≠ 0 := by
    have hh : Continuous (fun t : ℝ => x+t • u) := by fun_prop
    have hh0 : ContinuousAt (fun t : ℝ => x+t • u) 0 := hh.continuousAt
    have hh' := hh0.eventually_ne (by simpa using hx : x+(0:ℝ) • u ≠ 0)
    exact hh'
  have he : deriv (fun t : ℝ => f ‖x+t • u‖) =ᶠ[𝓝 0]
      fun t => deriv f ‖x+t • u‖*(⟪x+t • u,u⟫_ℝ/‖x+t • u‖) := by
    filter_upwards [hnear] with t ht
    have hp : 0 < ‖x+t • u‖ := norm_pos_iff.mpr ht
    exact (((hf _ hp).differentiableAt (Ioi_mem_nhds hp)).hasDerivAt.comp t
      (norm_line_hasDerivAt x u t ht)).deriv
  rw [(hd.congr_of_eventuallyEq he).deriv]
  simp only [zero_smul, add_zero]
  field_simp
  ring

theorem radial_euclidean_laplacian {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (f : ℝ → ℝ)
    (hf : DifferentiableOn ℝ f (Ioi 0)) (x : V) (hx : x ≠ 0)
    (hf₂ : DifferentiableAt ℝ (deriv f) ‖x‖) :
    euclideanLaplacian b (fun y => f ‖y‖) x =
      deriv (deriv f) ‖x‖+((Fintype.card ι:ℝ)-1)/‖x‖*deriv f ‖x‖ := by
  have hn := (norm_pos_iff.mpr hx).ne'
  have hs : (∑ i, ⟪x,b i⟫_ℝ^2)=‖x‖^2 := by
    simpa only [real_inner_comm (b _), ← sq, real_inner_self_eq_norm_sq] using
      b.sum_inner_mul_inner x x
  have hu (i : ι) : ‖b i‖=1 := b.orthonormal.1 i
  unfold euclideanLaplacian
  simp_rw [radial_direction_second_derivative f hf x _ hx hf₂, hu,
    one_pow, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_div, ← Finset.mul_sum]
  rw [hs]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  simp_rw [← Finset.sum_div, hs]
  field_simp
  ring

theorem radial_energy_hasFDerivAt (f : ℝ → ℝ) (x : V)
    (hf : DifferentiableAt ℝ f (‖x‖^2/2)) :
    HasFDerivAt (fun y : V => f (‖y‖^2/2))
      (deriv f (‖x‖^2/2) • innerSL ℝ x) x := by
  have hn := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_smul (1/2 : ℝ)
  have hn' : HasFDerivAt (fun y : V => ‖y‖^2/2) (innerSL ℝ x) x := by
    convert hn using 1
    · funext y; simp only [smul_eq_mul]; ring
    · ext u
      simp
  exact hf.hasDerivAt.comp_hasFDerivAt x hn'

/-- Actual Fréchet differentiation gives the Euclidean gradient vector. -/
theorem radial_energy_gradient (f : ℝ → ℝ) (x u : V)
    (hf : DifferentiableAt ℝ f (‖x‖^2/2)) :
    fderiv ℝ (fun y : V => f (‖y‖^2/2)) x u =
      ⟪deriv f (‖x‖^2/2) • x,u⟫_ℝ := by
  rw [(radial_energy_hasFDerivAt f x hf).fderiv]
  simp [real_inner_smul_left]

theorem radial_energy_direction_second_derivative_of_eventually (f : ℝ → ℝ) (x u : V)
    (hf : ∀ᶠ t : ℝ in 𝓝 0, DifferentiableAt ℝ f (‖x+t • u‖^2/2))
    (hf₂ : DifferentiableAt ℝ (deriv f) (‖x‖^2/2)) :
    deriv (deriv (fun t : ℝ => f (‖x+t • u‖^2/2))) 0 =
      deriv (deriv f) (‖x‖^2/2)*⟪x,u⟫_ℝ^2+
      deriv f (‖x‖^2/2)*‖u‖^2 := by
  have hl (t : ℝ) : HasDerivAt (fun s : ℝ => x+s • u) u t := by
    simpa using (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const u)
  have hn (t : ℝ) : HasDerivAt (fun s : ℝ => ‖x+s • u‖^2/2) ⟪x+t • u,u⟫_ℝ t := by
    convert (hl t).norm_sq.div_const 2 using 1
    ring
  have hn0 : HasDerivAt (fun s : ℝ => ‖x+s • u‖^2/2) ⟪x,u⟫_ℝ 0 := by
    simpa using hn 0
  have hinner : HasDerivAt (fun t : ℝ => ⟪x+t • u,u⟫_ℝ) (‖u‖^2) 0 := by
    simpa [real_inner_self_eq_norm_sq] using (hl 0).inner ℝ (hasDerivAt_const 0 u)
  have hf₂' : HasDerivAt (deriv f) (deriv (deriv f) (‖x‖^2/2))
      (‖x+(0:ℝ) • u‖^2/2) := by simpa using hf₂.hasDerivAt
  have hd := (hf₂'.comp 0 hn0).mul hinner
  simp only [Function.comp_def] at hd
  have he : deriv (fun t : ℝ => f (‖x+t • u‖^2/2)) =ᶠ[𝓝 0]
      fun t => deriv f (‖x+t • u‖^2/2)*⟪x+t • u,u⟫_ℝ := by
    filter_upwards [hf] with t ht
    exact (ht.hasDerivAt.comp t (hn t)).deriv
  rw [(hd.congr_of_eventuallyEq he).deriv]
  simp only [zero_smul, add_zero]
  ring

theorem radial_energy_direction_second_derivative (f : ℝ → ℝ)
    (hf : ∀ t ≥ 0, DifferentiableAt ℝ f t) (x u : V)
    (hf₂ : DifferentiableAt ℝ (deriv f) (‖x‖^2/2)) :
    deriv (deriv (fun t : ℝ => f (‖x+t • u‖^2/2))) 0 =
      deriv (deriv f) (‖x‖^2/2)*⟪x,u⟫_ℝ^2+
      deriv f (‖x‖^2/2)*‖u‖^2 :=
  radial_energy_direction_second_derivative_of_eventually f x u
    (Eventually.of_forall fun t => hf _ (by positivity)) hf₂

theorem radial_energy_direction_second_derivative_positive (f : ℝ → ℝ)
    (hf : DifferentiableOn ℝ f (Ioi 0)) (x u : V) (hx : x ≠ 0)
    (hf₂ : DifferentiableAt ℝ (deriv f) (‖x‖^2/2)) :
    deriv (deriv (fun t : ℝ => f (‖x+t • u‖^2/2))) 0 =
      deriv (deriv f) (‖x‖^2/2)*⟪x,u⟫_ℝ^2+
      deriv f (‖x‖^2/2)*‖u‖^2 := by
  apply radial_energy_direction_second_derivative_of_eventually f x u _ hf₂
  have hh0 : ContinuousAt (fun t : ℝ => x+t • u) 0 := by fun_prop
  filter_upwards [hh0.eventually_ne (by simpa using hx : x+(0:ℝ) • u ≠ 0)] with t ht
  have hp : 0 < ‖x+t • u‖^2/2 := div_pos (sq_pos_of_pos (norm_pos_iff.mpr ht)) (by norm_num)
  exact (hf _ hp).differentiableAt (Ioi_mem_nhds hp)

theorem radial_energy_euclidean_laplacian_positive {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (f : ℝ → ℝ)
    (hf : DifferentiableOn ℝ f (Ioi 0)) (x : V) (hx : x ≠ 0)
    (hf₂ : DifferentiableAt ℝ (deriv f) (‖x‖^2/2)) :
    euclideanLaplacian b (fun y => f (‖y‖^2/2)) x =
      ‖x‖^2*deriv (deriv f) (‖x‖^2/2)+(Fintype.card ι:ℝ)*deriv f (‖x‖^2/2) := by
  have hs : (∑ i, ⟪x,b i⟫_ℝ^2)=‖x‖^2 := by
    simpa only [real_inner_comm (b _), ← sq, real_inner_self_eq_norm_sq] using
      b.sum_inner_mul_inner x x
  have hu (i : ι) : ‖b i‖=1 := b.orthonormal.1 i
  unfold euclideanLaplacian
  simp_rw [radial_energy_direction_second_derivative_positive f hf x _ hx hf₂, hu, one_pow,
    mul_one, Finset.sum_add_distrib, ← Finset.mul_sum, hs]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

theorem radial_energy_OU_generator_positive {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (f : ℝ → ℝ)
    (hf : DifferentiableOn ℝ f (Ioi 0)) (x : V) (hx : x ≠ 0)
    (hf₂ : DifferentiableAt ℝ (deriv f) (‖x‖^2/2)) :
    (1/2:ℝ)*euclideanLaplacian b (fun y => f (‖y‖^2/2)) x-
      (1/2:ℝ)*fderiv ℝ (fun y : V => f (‖y‖^2/2)) x x =
      (‖x‖^2/2)*deriv (deriv f) (‖x‖^2/2)+
        ((Fintype.card ι:ℝ)/2-‖x‖^2/2)*deriv f (‖x‖^2/2) := by
  have hp : 0 < ‖x‖^2/2 := div_pos (sq_pos_of_pos (norm_pos_iff.mpr hx)) (by norm_num)
  rw [radial_energy_euclidean_laplacian_positive b f hf x hx hf₂,
    radial_energy_gradient f x x ((hf _ hp).differentiableAt (Ioi_mem_nhds hp)),
    real_inner_smul_left, real_inner_self_eq_norm_sq]
  ring

theorem radial_energy_euclidean_laplacian {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (f : ℝ → ℝ)
    (hf : ∀ t ≥ 0, DifferentiableAt ℝ f t) (x : V)
    (hf₂ : DifferentiableAt ℝ (deriv f) (‖x‖^2/2)) :
    euclideanLaplacian b (fun y => f (‖y‖^2/2)) x =
      ‖x‖^2*deriv (deriv f) (‖x‖^2/2)+(Fintype.card ι:ℝ)*deriv f (‖x‖^2/2) := by
  have hs : (∑ i, ⟪x,b i⟫_ℝ^2)=‖x‖^2 := by
    simpa only [real_inner_comm (b _), ← sq, real_inner_self_eq_norm_sq] using
      b.sum_inner_mul_inner x x
  have hu (i : ι) : ‖b i‖=1 := b.orthonormal.1 i
  unfold euclideanLaplacian
  simp_rw [radial_energy_direction_second_derivative f hf x _ hf₂, hu, one_pow,
    mul_one, Finset.sum_add_distrib, ← Finset.mul_sum, hs]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- The supplied Euclidean OU differential operator, evaluated on radial energy. -/
theorem radial_energy_OU_generator {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (f : ℝ → ℝ)
    (hf : ∀ t ≥ 0, DifferentiableAt ℝ f t) (x : V)
    (hf₂ : DifferentiableAt ℝ (deriv f) (‖x‖^2/2)) :
    (1/2:ℝ)*euclideanLaplacian b (fun y => f (‖y‖^2/2)) x-
      (1/2:ℝ)*fderiv ℝ (fun y : V => f (‖y‖^2/2)) x x =
      (‖x‖^2/2)*deriv (deriv f) (‖x‖^2/2)+
        ((Fintype.card ι:ℝ)/2-‖x‖^2/2)*deriv f (‖x‖^2/2) := by
  rw [radial_energy_euclidean_laplacian b f hf x hf₂,
    radial_energy_gradient f x x (hf _ (by positivity)),
    real_inner_smul_left, real_inner_self_eq_norm_sq]
  ring

end
end Sigma
