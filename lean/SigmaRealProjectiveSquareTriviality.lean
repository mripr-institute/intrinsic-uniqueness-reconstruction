import SigmaRealProjectiveComplexification
import Mathlib.Topology.Constructions
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional

namespace Sigma
noncomputable section
open TensorProduct
open scoped BigOperators

abbrev RealProjectiveTensorSquareAmbient := (Fin 3 × Fin 3) → ℂ

/-- The tensor-square generator in the ambient tensor-coordinate space. -/
def realProjectiveTensorSquareGenerator (p : RealProjectivePlane) :
    RealProjectiveTensorSquareAmbient :=
  fun ij => (p.rep ij.1 : ℂ) * (p.rep ij.2 : ℂ)

/-- The actual incidence fiber of the tensor square of the projective line. -/
def realProjectiveTensorSquareFiber (p : RealProjectivePlane) :
    Submodule ℂ RealProjectiveTensorSquareAmbient :=
  ℂ ∙ realProjectiveTensorSquareGenerator p

/-- The rank-one orthogonal projector, viewed as a tensor-square vector. -/
def realProjectiveTensorSquareProjector (p : RealProjectivePlane) :
    RealProjectiveTensorSquareAmbient :=
  fun ij => (realProjectiveProjector p ij.1 ij.2 : ℂ)

private def realProjectiveRepSquareSum (p : RealProjectivePlane) : ℝ :=
  realVectorSquare p.rep

private theorem real_projective_rep_square_sum_pos (p : RealProjectivePlane) :
    0 < realProjectiveRepSquareSum p := by
  exact real_vector_square_pos p.rep_nonzero

private theorem real_projective_tensor_square_projector_formula
    (p : RealProjectivePlane) (ij : Fin 3 × Fin 3) :
    realProjectiveTensorSquareProjector p ij =
      ((realProjectiveRepSquareSum p : ℂ)⁻¹) * realProjectiveTensorSquareGenerator p ij := by
  change (realProjectiveProjector p ij.1 ij.2 : ℂ) = _
  conv_lhs => rw [← p.mk_rep, real_projective_projector_mk]
  simp only [realProjectiveTensorSquareGenerator]
  push_cast
  simp only [realProjectiveRepSquareSum]
  field_simp [ne_of_gt (real_projective_rep_square_sum_pos p)]

private theorem real_projective_tensor_square_projector_mem
    (p : RealProjectivePlane) :
    realProjectiveTensorSquareProjector p ∈ realProjectiveTensorSquareFiber p := by
  rw [realProjectiveTensorSquareFiber, Submodule.mem_span_singleton]
  refine ⟨(realProjectiveRepSquareSum p : ℂ)⁻¹, ?_⟩
  funext ij
  simpa [smul_eq_mul] using (real_projective_tensor_square_projector_formula p ij).symm

private theorem real_projective_tensor_square_projector_continuous :
    Continuous realProjectiveTensorSquareProjector := by
  apply continuous_pi
  intro ij
  exact Complex.continuous_ofReal.comp
    (real_projective_projector_continuous ij.1 ij.2)

private theorem real_projective_tensor_square_projector_ne_zero
    (p : RealProjectivePlane) : realProjectiveTensorSquareProjector p ≠ 0 := by
  intro h
  have hex : ∃ i : Fin 3, p.rep i ≠ 0 := by
    by_contra hn
    apply p.rep_nonzero
    funext i
    simpa using not_exists.mp hn i
  obtain ⟨i, hi⟩ := hex
  have hd := congrFun h (i, i)
  change (realProjectiveProjector p i i : ℂ) = 0 at hd
  conv at hd => lhs; rw [← p.mk_rep, real_projective_projector_mk]
  have hs : 0 < realProjectiveRepSquareSum p := real_projective_rep_square_sum_pos p
  have hn : p.rep i ^ 2 / realProjectiveRepSquareSum p ≠ 0 := by
    apply div_ne_zero
    · exact pow_ne_zero _ hi
    · exact ne_of_gt hs
  apply hn
  have hz := Complex.ofReal_eq_zero.mp hd
  simpa [realProjectiveRepSquareSum] using hz

private theorem real_projective_tensor_square_projector_norm_sq
    (p : RealProjectivePlane) :
    ∑ ij : Fin 3 × Fin 3, ‖realProjectiveTensorSquareProjector p ij‖ ^ 2 = 1 := by
  have hreal (i j : Fin 3) :
      ‖realProjectiveTensorSquareProjector p (i, j)‖ ^ 2 =
        ((p.rep i * p.rep j / realProjectiveRepSquareSum p) ^ 2) := by
    change ‖(realProjectiveProjector p i j : ℂ)‖ ^ 2 = _
    conv_lhs => rw [← p.mk_rep, real_projective_projector_mk]
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    simp [realProjectiveRepSquareSum]
  have hnum : (∑ i : Fin 3, ∑ j : Fin 3,
      (p.rep i * p.rep j) ^ 2) = (realProjectiveRepSquareSum p) ^ 2 := by
    simp only [mul_pow]
    rw [← Finset.sum_mul_sum]
    simp only [realProjectiveRepSquareSum, realVectorSquare]
    ring
  rw [Fintype.sum_prod_type]
  simp_rw [hreal]
  simp_rw [div_pow]
  simp_rw [← Finset.sum_div]
  rw [hnum]
  field_simp [ne_of_gt (real_projective_rep_square_sum_pos p)]

/-
private def realProjectiveTensorSquareTotalSpace :=
  {z : RealProjectivePlane × RealProjectiveTensorSquareAmbient //
    z.2 ∈ realProjectiveTensorSquareFiber z.1}

private def realProjectiveTensorSquareCoordinate
    (z : realProjectiveTensorSquareTotalSpace) : ℂ :=
  ∑ ij : Fin 3 × Fin 3,
    star (realProjectiveTensorSquareProjector z.1.1 ij) * z.1.2 ij

private def realProjectiveTensorSquareTrivializeFun
    (z : realProjectiveTensorSquareTotalSpace) : RealProjectivePlane × ℂ :=
  (z.1.1, realProjectiveTensorSquareCoordinate z)

private def realProjectiveTensorSquareTrivializeInvFun
    (p : RealProjectivePlane × ℂ) : realProjectiveTensorSquareTotalSpace :=
  ⟨(p.1, p.2 • realProjectiveTensorSquareProjector p.1), by
    exact Submodule.smul_mem _ p.2 (real_projective_tensor_square_projector_mem p.1)⟩

private theorem real_projective_tensor_square_coordinate_smul
    (p : RealProjectivePlane) (c : ℂ) :
    realProjectiveTensorSquareCoordinate
      ⟨(p, c • realProjectiveTensorSquareProjector p),
        (real_projectiveTensorSquareProjector_mem p).smul c⟩ = c := by
  simp only [realProjectiveTensorSquareCoordinate, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  have hnorm := real_projective_tensor_square_projector_norm_sq p
  simp_rw [realProjectiveTensorSquareProjector]
  rw [← Complex.ofReal_one, ← hnorm]
  simp only [Complex.norm_eq_abs, abs_of_nonneg (by positivity :
    0 ≤ ‖realProjectiveTensorSquareProjector p (·)‖ ^ 2)] at *
  -- The projector has real entries, so its Hermitian square sum is its real norm square.
  simp [realProjectiveTensorSquareProjector, ← Complex.ofReal_mul,
    ← Complex.ofReal_sum, realProjectiveTensorSquareProjector_norm_sq]
-/

structure NonvanishingRealProjectiveTensorSquareSection where
  value : RealProjectivePlane → RealProjectiveTensorSquareAmbient
  continuous_value : Continuous value
  fiber : ∀ p, value p ∈ realProjectiveTensorSquareFiber p
  nonzero : ∀ p, value p ≠ 0

/-- The orthogonal projector is a continuous, nowhere-zero section of the actual
incidence line spanned by the tensor-square of the tautological vector. -/
def realProjectiveTensorSquareSection : NonvanishingRealProjectiveTensorSquareSection where
  value := realProjectiveTensorSquareProjector
  continuous_value := real_projective_tensor_square_projector_continuous
  fiber := real_projective_tensor_square_projector_mem
  nonzero := real_projective_tensor_square_projector_ne_zero

private theorem real_projective_tensor_square_projector_inner_one
    (p : RealProjectivePlane) :
    ∑ ij : Fin 3 × Fin 3,
      star (realProjectiveTensorSquareProjector p ij) *
        realProjectiveTensorSquareProjector p ij = 1 := by
  have hterm (ij : Fin 3 × Fin 3) :
      star (realProjectiveTensorSquareProjector p ij) *
          realProjectiveTensorSquareProjector p ij =
        (‖realProjectiveTensorSquareProjector p ij‖ ^ 2 : ℂ) := by
    let r := realProjectiveProjector p ij.1 ij.2
    change star (r : ℂ) * (r : ℂ) = (‖(r : ℂ)‖ ^ 2 : ℂ)
    calc
      _ = ((r * r : ℝ) : ℂ) := by simp
      _ = ((|r| ^ 2 : ℝ) : ℂ) := by
        congr 1
        rw [sq_abs]
        ring
      _ = _ := by
        simp only [Complex.norm_real, Real.norm_eq_abs]
        norm_cast
  calc
    _ = ∑ ij : Fin 3 × Fin 3,
        (‖realProjectiveTensorSquareProjector p ij‖ ^ 2 : ℂ) := by
      apply Finset.sum_congr rfl
      intro ij hij
      exact hterm ij
    _ = (∑ ij : Fin 3 × Fin 3,
        ‖realProjectiveTensorSquareProjector p ij‖ ^ 2 : ℝ) := by
      rw [Complex.ofReal_sum]
      simp only [Complex.ofReal_pow]
    _ = 1 := by exact_mod_cast real_projective_tensor_square_projector_norm_sq p

abbrev realProjectiveTensorSquareTotalSpace :=
  {z : RealProjectivePlane × RealProjectiveTensorSquareAmbient //
    z.2 ∈ realProjectiveTensorSquareFiber z.1}

private def realProjectiveTensorSquareCoordinate
    (z : realProjectiveTensorSquareTotalSpace) : ℂ :=
  ∑ ij : Fin 3 × Fin 3,
    star (realProjectiveTensorSquareProjector z.1.1 ij) * z.1.2 ij

private def realProjectiveTensorSquareTrivializeInvFun
    (p : RealProjectivePlane × ℂ) : realProjectiveTensorSquareTotalSpace :=
  ⟨(p.1, p.2 • realProjectiveTensorSquareProjector p.1),
    Submodule.smul_mem _ p.2 (real_projective_tensor_square_projector_mem p.1)⟩

private theorem real_projective_tensor_square_coordinate_smul
    (p : RealProjectivePlane) (c : ℂ) :
    realProjectiveTensorSquareCoordinate
      (realProjectiveTensorSquareTrivializeInvFun (p, c)) = c := by
  simp only [realProjectiveTensorSquareCoordinate,
    realProjectiveTensorSquareTrivializeInvFun, Subtype.coe_mk,
    Pi.smul_apply, smul_eq_mul]
  calc
    _ = ∑ ij : Fin 3 × Fin 3,
        c * (star (realProjectiveTensorSquareProjector p ij) *
          realProjectiveTensorSquareProjector p ij) := by
      apply Finset.sum_congr rfl
      intro ij hij
      ring
    _ = c * ∑ ij : Fin 3 × Fin 3,
        star (realProjectiveTensorSquareProjector p ij) *
          realProjectiveTensorSquareProjector p ij := by rw [Finset.mul_sum]
    _ = c := by rw [real_projective_tensor_square_projector_inner_one, mul_one]

private theorem real_projective_tensor_square_generator_eq_norm_smul_projector
    (p : RealProjectivePlane) :
    (realProjectiveRepSquareSum p : ℂ) • realProjectiveTensorSquareProjector p =
      realProjectiveTensorSquareGenerator p := by
  funext ij
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [real_projective_tensor_square_projector_formula]
  field_simp [ne_of_gt (real_projective_rep_square_sum_pos p)]

private theorem real_projective_tensor_square_reconstruct
    (z : realProjectiveTensorSquareTotalSpace) :
    z.1.2 = realProjectiveTensorSquareCoordinate z •
      realProjectiveTensorSquareProjector z.1.1 := by
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp z.2
  have hgen := real_projective_tensor_square_generator_eq_norm_smul_projector z.1.1
  have hvec : z.1.2 =
      (d * (realProjectiveRepSquareSum z.1.1 : ℂ)) •
        realProjectiveTensorSquareProjector z.1.1 := by
    rw [← hd, ← hgen, smul_smul]
  have hcoord : realProjectiveTensorSquareCoordinate z =
      d * (realProjectiveRepSquareSum z.1.1 : ℂ) := by
    have hz : z = realProjectiveTensorSquareTrivializeInvFun
        (z.1.1, d * (realProjectiveRepSquareSum z.1.1 : ℂ)) := by
      apply Subtype.ext
      exact Prod.ext rfl hvec
    rw [hz]
    exact real_projective_tensor_square_coordinate_smul _ _
  rw [hvec, hcoord]

private def realProjectiveTensorSquareTrivializeFun
    (z : realProjectiveTensorSquareTotalSpace) : RealProjectivePlane × ℂ :=
  (z.1.1, realProjectiveTensorSquareCoordinate z)

private def realProjectiveTensorSquareTrivialization :
    realProjectiveTensorSquareTotalSpace ≃ₜ (RealProjectivePlane × ℂ) where
  toFun := realProjectiveTensorSquareTrivializeFun
  invFun := realProjectiveTensorSquareTrivializeInvFun
  left_inv z := by
    apply Subtype.ext
    exact Prod.ext rfl (real_projective_tensor_square_reconstruct z).symm
  right_inv p := by
    change (p.1, realProjectiveTensorSquareCoordinate
      (realProjectiveTensorSquareTrivializeInvFun p)) = p
    exact Prod.ext rfl (real_projective_tensor_square_coordinate_smul p.1 p.2)
  continuous_toFun := by
    have hb : Continuous (fun z : realProjectiveTensorSquareTotalSpace => z.1.1) :=
      continuous_fst.comp continuous_subtype_val
    have hP : Continuous (fun z : realProjectiveTensorSquareTotalSpace =>
        realProjectiveTensorSquareProjector z.1.1) :=
      real_projective_tensor_square_projector_continuous.comp hb
    have hv : Continuous (fun z : realProjectiveTensorSquareTotalSpace => z.1.2) :=
      continuous_snd.comp continuous_subtype_val
    have hc : Continuous realProjectiveTensorSquareCoordinate := by
      unfold realProjectiveTensorSquareCoordinate
      apply continuous_finset_sum Finset.univ
      intro ij hij
      exact ((continuous_star.comp ((continuous_apply ij).comp hP)).mul
        ((continuous_apply ij).comp hv))
    exact hb.prod_mk hc
  continuous_invFun := by
    have hb : Continuous (fun p : RealProjectivePlane × ℂ => p.1) := continuous_fst
    have hc : Continuous (fun p : RealProjectivePlane × ℂ => p.2) := continuous_snd
    have hP : Continuous (fun p : RealProjectivePlane × ℂ =>
        realProjectiveTensorSquareProjector p.1) :=
      real_projective_tensor_square_projector_continuous.comp hb
    have hv : Continuous (fun p : RealProjectivePlane × ℂ =>
        p.2 • realProjectiveTensorSquareProjector p.1) := hc.smul hP
    exact (hb.prod_mk hv).subtype_mk (fun p =>
      Submodule.smul_mem _ p.2 (real_projective_tensor_square_projector_mem p.1))

private def realProjectiveTensorSquareFiberCoordinate (p : RealProjectivePlane)
    (w : realProjectiveTensorSquareFiber p) : ℂ :=
  realProjectiveTensorSquareCoordinate ⟨(p, w.1), w.2⟩

private theorem real_projective_tensor_square_fiber_reconstruct
    (p : RealProjectivePlane) (w : realProjectiveTensorSquareFiber p) :
    w.1 = realProjectiveTensorSquareFiberCoordinate p w •
      realProjectiveTensorSquareProjector p := by
  have h := real_projective_tensor_square_reconstruct ⟨(p, w.1), w.2⟩
  simpa [realProjectiveTensorSquareFiberCoordinate] using h

private theorem real_projective_tensor_square_fiber_coordinate_smul
    (p : RealProjectivePlane) (c : ℂ) :
    realProjectiveTensorSquareFiberCoordinate p
      ⟨c • realProjectiveTensorSquareProjector p,
        Submodule.smul_mem _ c (real_projective_tensor_square_projector_mem p)⟩ = c := by
  simpa [realProjectiveTensorSquareFiberCoordinate,
    realProjectiveTensorSquareTrivializeInvFun] using
      (real_projective_tensor_square_coordinate_smul p c)

private def realProjectiveTensorSquareFiberCoordinateLinearMap (p : RealProjectivePlane) :
    realProjectiveTensorSquareFiber p →ₗ[ℂ] ℂ where
  toFun := realProjectiveTensorSquareFiberCoordinate p
  map_add' x y := by
    simp only [realProjectiveTensorSquareFiberCoordinate,
      realProjectiveTensorSquareCoordinate, Submodule.coe_add, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ij hij
    ring
  map_smul' c x := by
    simp only [realProjectiveTensorSquareFiberCoordinate,
      realProjectiveTensorSquareCoordinate, Submodule.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    calc
      _ = ∑ ij : Fin 3 × Fin 3,
          c * (star (realProjectiveTensorSquareProjector p ij) * x.1 ij) := by
        apply Finset.sum_congr rfl
        intro ij hij
        ring
      _ = c * ∑ ij : Fin 3 × Fin 3,
          star (realProjectiveTensorSquareProjector p ij) * x.1 ij := by
        rw [Finset.mul_sum]

private theorem real_projective_tensor_square_fiber_coordinate_bijective
    (p : RealProjectivePlane) :
    Function.Bijective (realProjectiveTensorSquareFiberCoordinateLinearMap p) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    change realProjectiveTensorSquareFiberCoordinate p x =
      realProjectiveTensorSquareFiberCoordinate p y at hxy
    calc
      x.1 = realProjectiveTensorSquareFiberCoordinate p x •
          realProjectiveTensorSquareProjector p :=
        real_projective_tensor_square_fiber_reconstruct p x
      _ = realProjectiveTensorSquareFiberCoordinate p y •
          realProjectiveTensorSquareProjector p := by rw [hxy]
      _ = y.1 := (real_projective_tensor_square_fiber_reconstruct p y).symm
  · intro c
    refine ⟨⟨c • realProjectiveTensorSquareProjector p,
      Submodule.smul_mem _ c (real_projective_tensor_square_projector_mem p)⟩, ?_⟩
    exact real_projective_tensor_square_fiber_coordinate_smul p c

private def realProjectiveTensorSquareFiberEquiv (p : RealProjectivePlane) :
    realProjectiveTensorSquareFiber p ≃ₗ[ℂ] ℂ :=
  LinearEquiv.ofBijective (realProjectiveTensorSquareFiberCoordinateLinearMap p)
    (real_projective_tensor_square_fiber_coordinate_bijective p)

/-- A genuine trivialization of the tensor-square incidence bundle. Its total
space has the subspace topology from the ambient tensor bundle, and its fiber
maps are complex-linear equivalences. -/
structure RealProjectiveTensorSquareBundleTrivialization where
  totalHomeomorph : realProjectiveTensorSquareTotalSpace ≃ₜ
    (RealProjectivePlane × ℂ)
  fiberEquiv : ∀ p, realProjectiveTensorSquareFiber p ≃ₗ[ℂ] ℂ
  total_apply : ∀ (p : RealProjectivePlane)
      (w : realProjectiveTensorSquareFiber p),
    totalHomeomorph ⟨(p, w.1), w.2⟩ = (p, fiberEquiv p w)

/-- The complexified tautological line's tensor square is trivial: the normalized
rank-one projector gives a global nonzero section and an explicit trivialization. -/
def realProjectiveComplexificationTensorSquareTrivialization :
    RealProjectiveTensorSquareBundleTrivialization where
  totalHomeomorph := realProjectiveTensorSquareTrivialization
  fiberEquiv := realProjectiveTensorSquareFiberEquiv
  total_apply := by
    intro p w
    rfl

private theorem real_projective_tensor_coordinate_mem
    (p : RealProjectivePlane)
    (x y : (realProjectiveComplexification p).submodule) :
    (fun ij : Fin 3 × Fin 3 => x.1 ij.1 * y.1 ij.2) ∈
      realProjectiveTensorSquareFiber p := by
  have hx : x.1 ∈ ℂ ∙ realCoordinateComplexification p.rep := by
    rw [← real_projective_complexification_fiber p]
    exact x.2
  have hy : y.1 ∈ ℂ ∙ realCoordinateComplexification p.rep := by
    rw [← real_projective_complexification_fiber p]
    exact y.2
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hy
  rw [realProjectiveTensorSquareFiber, Submodule.mem_span_singleton]
  refine ⟨a * b, ?_⟩
  funext ij
  change (a * b) *
    ((p.rep ij.1 : ℂ) * (p.rep ij.2 : ℂ)) = x.1 ij.1 * y.1 ij.2
  rw [← ha, ← hb]
  change (a * b) * ((p.rep ij.1 : ℂ) * (p.rep ij.2 : ℂ)) =
    (a * (p.rep ij.1 : ℂ)) * (b * (p.rep ij.2 : ℂ))
  ring

private def realProjectiveTensorSquareBilinear (p : RealProjectivePlane) :
    (realProjectiveComplexification p).submodule →ₗ[ℂ]
      (realProjectiveComplexification p).submodule →ₗ[ℂ]
        realProjectiveTensorSquareFiber p where
  toFun x := {
    toFun := fun y => ⟨fun ij => x.1 ij.1 * y.1 ij.2,
      real_projective_tensor_coordinate_mem p x y⟩
    map_add' := by
      intro y z
      apply Subtype.ext
      funext ij
      simp [mul_add]
    map_smul' := by
      intro c y
      apply Subtype.ext
      funext ij
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
      simp only [RingHom.id_apply]
      ring
  }
  map_add' := by
    intro x y
    ext z
    simp [add_mul]
  map_smul' := by
    intro c x
    ext y
    simp [mul_assoc]

private def realProjectiveComplexTensorSquareMap (p : RealProjectivePlane) :
    (realProjectiveComplexification p).submodule ⊗[ℂ]
      (realProjectiveComplexification p).submodule →ₗ[ℂ]
        realProjectiveTensorSquareFiber p :=
  TensorProduct.lift (realProjectiveTensorSquareBilinear p)

theorem real_projective_complex_tensor_square_map_tmul
    (p : RealProjectivePlane)
    (x y : (realProjectiveComplexification p).submodule) :
    realProjectiveComplexTensorSquareMap p (x ⊗ₜ[ℂ] y) =
      ⟨(fun ij : Fin 3 × Fin 3 => x.1 ij.1 * y.1 ij.2),
        real_projective_tensor_coordinate_mem p x y⟩ := by
  simp [realProjectiveComplexTensorSquareMap, TensorProduct.lift.tmul,
    realProjectiveTensorSquareBilinear]

private theorem real_projective_tensor_square_generator_ne_zero
    (p : RealProjectivePlane) : realProjectiveTensorSquareGenerator p ≠ 0 := by
  intro hz
  have hex : ∃ i : Fin 3, p.rep i ≠ 0 := by
    by_contra h
    apply p.rep_nonzero
    funext i
    simpa using not_exists.mp h i
  obtain ⟨i, hi⟩ := hex
  have hz' := congrFun hz (i, i)
  change (p.rep i : ℂ) * (p.rep i : ℂ) = 0 at hz'
  exact (mul_ne_zero (Complex.ofReal_ne_zero.mpr hi)
    (Complex.ofReal_ne_zero.mpr hi)) hz'

private theorem real_projective_complex_tensor_square_map_surjective
    (p : RealProjectivePlane) :
    Function.Surjective (realProjectiveComplexTensorSquareMap p) := by
  intro w
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp w.2
  let v : (realProjectiveComplexification p).submodule :=
    ⟨realCoordinateComplexification p.rep, by
      rw [real_projective_complexification_fiber p]
      exact Submodule.mem_span_singleton_self _⟩
  have hv : realProjectiveComplexTensorSquareMap p (v ⊗ₜ[ℂ] v) =
      ⟨realProjectiveTensorSquareGenerator p,
        Submodule.mem_span_singleton_self _⟩ := by
    apply Subtype.ext
    funext ij
    rfl
  refine ⟨c • (v ⊗ₜ[ℂ] v), ?_⟩
  calc
    realProjectiveComplexTensorSquareMap p (c • (v ⊗ₜ[ℂ] v)) =
        c • realProjectiveComplexTensorSquareMap p (v ⊗ₜ[ℂ] v) := map_smul _ _ _
    _ = c • ⟨realProjectiveTensorSquareGenerator p,
        Submodule.mem_span_singleton_self _⟩ := by rw [hv]
    _ = w := Subtype.ext hc

private theorem real_projective_complex_tensor_square_map_bijective
    (p : RealProjectivePlane) :
    Function.Bijective (realProjectiveComplexTensorSquareMap p) := by
  have hline : Module.finrank ℂ (realProjectiveComplexification p).submodule = 1 :=
    real_projective_complex_fiber_finrank p
  have hfiber : Module.finrank ℂ (realProjectiveTensorSquareFiber p) = 1 := by
    rw [realProjectiveTensorSquareFiber, finrank_span_singleton
      (real_projective_tensor_square_generator_ne_zero p)]
  have hdim : Module.finrank ℂ
      ((realProjectiveComplexification p).submodule ⊗[ℂ]
        (realProjectiveComplexification p).submodule) =
      Module.finrank ℂ (realProjectiveTensorSquareFiber p) := by
    rw [Module.finrank_tensorProduct, hline, hfiber]
  have hsurj := real_projective_complex_tensor_square_map_surjective p
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj
  exact ⟨hinj, hsurj⟩

/-- The concrete incidence fiber is canonically the algebraic tensor square of
the actual complexification line, not merely a fiberwise scalar model. -/
def realProjectiveComplexTensorSquareFiberEquiv (p : RealProjectivePlane) :
    (realProjectiveComplexification p).submodule ⊗[ℂ]
      (realProjectiveComplexification p).submodule ≃ₗ[ℂ]
        realProjectiveTensorSquareFiber p :=
  LinearEquiv.ofBijective (realProjectiveComplexTensorSquareMap p)
    (real_projective_complex_tensor_square_map_bijective p)

end
end Sigma
