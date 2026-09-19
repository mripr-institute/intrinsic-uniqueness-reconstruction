import SigmaAutomorphisms
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Data.Real.Irrational

namespace Sigma
noncomputable section
open Set

/-- A rational-linear projection yields an explicit non-real-linear additive
bijection, rather than assuming that an exotic automorphism exists. -/
theorem nonlinear_additive_bijection :
    ∃ A : ℝ ≃+ ℝ, ¬ ∃ c : ℝ, ∀ x, A x=c*x := by
  let ι : ℚ →ₗ[ℚ] ℝ :=
    { toFun := fun q => (q:ℝ)
      map_add' := by intros; push_cast; rfl
      map_smul' := by intros; simp [Rat.smul_def, smul_eq_mul] }
  have hι : LinearMap.ker ι=⊥ := LinearMap.ker_eq_bot.mpr Rat.cast_injective
  obtain ⟨p,hp⟩ := ι.exists_leftInverse_of_injective hι
  have hpr (q : ℚ) : p (q:ℝ)=q := congrArg (fun f : ℚ →ₗ[ℚ] ℚ => f q) hp
  let P : ℝ →ₗ[ℚ] ℝ := ι.comp p
  have hP (x : ℝ) : P (P x)=P x := by
    change (p (p x : ℝ) : ℝ)=(p x : ℝ)
    rw [hpr]
  have hP1 : P 1=1 := by
    change (p 1 : ℝ)=1
    rw [show (1:ℝ)=(1:ℚ) by norm_num, hpr]
  let A : ℝ ≃+ ℝ :=
    { toFun := fun x => x+P x
      invFun := fun x => x-(1/2 : ℚ) • P x
      left_inv := by
        intro x
        simp only [map_add, hP, map_smul, Rat.smul_def, smul_eq_mul, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
        ring
      right_inv := by
        intro x
        change x-(1/2 : ℚ) • P x+P (x-(1/2 : ℚ) • P x)=x
        rw [map_sub, map_smul, hP]
        simp only [Rat.smul_def, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
        ring
      map_add' := by intro x y; simp only [map_add]; ring }
  refine ⟨A, ?_⟩
  rintro ⟨c,hc⟩
  have hc2 : c=2 := by
    have h := hc 1
    change 1+P 1=c*1 at h
    rw [hP1] at h
    linarith
  have hx := hc (Real.sqrt 2)
  change Real.sqrt 2+(p (Real.sqrt 2):ℝ)=c*Real.sqrt 2 at hx
  rw [hc2] at hx
  have he : (p (Real.sqrt 2):ℝ)=Real.sqrt 2 := by linarith
  exact irrational_sqrt_two ⟨p (Real.sqrt 2), he⟩

def additiveConjugate (A : ℝ ≃+ ℝ) (x : ℝ) : ℝ :=
  Real.exp (A (Real.log (1+x)))-1

theorem additive_conjugate_closed (A : ℝ ≃+ ℝ) (x : ℝ) : -1 < additiveConjugate A x := by
  unfold additiveConjugate
  linarith [Real.exp_pos (A (Real.log (1+x)))]

theorem additive_conjugate_hom (A : ℝ ≃+ ℝ) (x y : ℝ) (hx : -1 < x) (hy : -1 < y) :
    additiveConjugate A (star x y)=star (additiveConjugate A x) (additiveConjugate A y) := by
  unfold additiveConjugate
  rw [SigmaBase.log_star hx hy, map_add, Real.exp_add]
  unfold star SigmaBase.star
  ring

theorem additive_conjugate_inverse (A : ℝ ≃+ ℝ) (x : ℝ) (hx : -1 < x) :
    additiveConjugate A.symm (additiveConjugate A x)=x ∧
    additiveConjugate A (additiveConjugate A.symm x)=x := by
  have hi (B : ℝ ≃+ ℝ) : additiveConjugate B.symm (additiveConjugate B x)=x := by
    unfold additiveConjugate
    rw [show 1+(Real.exp (B (Real.log (1+x)))-1)=Real.exp (B (Real.log (1+x))) by ring,
      Real.log_exp, B.symm_apply_apply, Real.exp_log (by linarith : 0 < 1+x)]
    ring
  exact ⟨hi A, hi A.symm⟩

theorem wild_group_automorphism :
    ∃ F G : ℝ → ℝ,
      (∀ x > -1, -1 < F x ∧ -1 < G x) ∧
      (∀ x > -1, ∀ y > -1, F (star x y)=star (F x) (F y)) ∧
      (∀ x > -1, G (F x)=x ∧ F (G x)=x) ∧
      ¬ ∃ c : ℝ, ∀ x > -1, F x=groupPower c x := by
  obtain ⟨A,hA⟩ := nonlinear_additive_bijection
  refine ⟨additiveConjugate A, additiveConjugate A.symm,
    fun x _ => ⟨additive_conjugate_closed A x, additive_conjugate_closed A.symm x⟩,
    fun x hx y hy => additive_conjugate_hom A x y hx hy,
    fun x hx => additive_conjugate_inverse A x hx, ?_⟩
  rintro ⟨c,hc⟩
  apply hA
  refine ⟨c, ?_⟩
  intro u
  have h := hc (Real.exp u-1) (by linarith [Real.exp_pos u])
  simp only [additiveConjugate, groupPower,
    show 1+(Real.exp u-1)=Real.exp u by ring, Real.log_exp] at h
  exact Real.exp_injective (by linarith)

end
end Sigma
