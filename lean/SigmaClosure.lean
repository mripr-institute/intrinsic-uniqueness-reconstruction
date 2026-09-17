import SigmaArchitecture
import SigmaRealOrthogonal

/-!
Section 9: exact reconstruction bookkeeping and concrete deletion boundaries.

This module does not stand in for the full enumeration in Theorems 9.2--9.5.
The transport results concern already proved equivalences. The concrete results
below establish the intrinsic component inverses, both placement deletion tests,
and the spatial conclusions and countermodels. The remaining analytic,
probabilistic, operator, and topological instances require their local proofs.
-/

namespace Sigma.Closure
noncomputable section

abbrev PositiveCoordinate := {t : ℝ // 0 < t}
abbrev ScalarFunction := PositiveCoordinate → ℝ
abbrev PositiveFunction := {q : ScalarFunction // ∀ t, 0 < q t}

/-- The intrinsic loss coordinate is exactly reversible. -/
def lossEquivalence : ScalarFunction ≃ ScalarFunction where
  toFun F := fun t => -F t
  invFun J := fun t => -J t
  left_inv F := by funext t; simp
  right_inv J := by funext t; simp

/-- Positivity is precisely the domain needed by the logarithmic inverse. -/
def densityEquivalence : ScalarFunction ≃ PositiveFunction where
  toFun F := ⟨fun t => Real.exp (F t - 1), fun t => Real.exp_pos _⟩
  invFun q := fun t => 1 + Real.log (q.1 t)
  left_inv F := by funext t; simp
  right_inv q := by
    apply Subtype.ext
    funext t
    simp only [add_sub_cancel_left, Real.exp_log (q.2 t)]

theorem intrinsic_loss_reconstruction :
    lossEquivalence (fun t => H t) = (fun t : PositiveCoordinate => I t) := by
  funext t
  change -SigmaPresentations.H t = SigmaBase.potential t
  rw [SigmaPresentations.H_eq_neg_potential]
  simp

theorem intrinsic_density_reconstruction :
    (densityEquivalence (fun t => H t)).1 = (fun t : PositiveCoordinate => p t) := by
  funext t
  exact (SigmaPresentations.density_eq_exp_H t.2).symm

theorem intrinsic_density_inverse :
    densityEquivalence.symm
      ⟨(fun t => p t), fun t => SigmaPresentations.density_pos t.2⟩ =
      (fun t : PositiveCoordinate => H t) := by
  funext t
  exact (intrinsic_log_density t.2).symm

/-- Pairwise transport has no extra compatibility hypothesis. -/
theorem presentation_transport_composes {S A B C : Type*}
    (eA : S ≃ A) (eB : S ≃ B) (eC : S ≃ C) (a : A) :
    presentationEquivalence eB eC (presentationEquivalence eA eB a) =
      presentationEquivalence eA eC a := by
  simp [presentationEquivalence]

/-- Uniqueness of the intrinsic value recovered from each complete presentation. -/
theorem presentation_intrinsic_unique {S A : Type*} (e : S ≃ A) (a : A) :
    ∃! s : S, e s = a := by
  refine ⟨e.symm a, e.apply_symm_apply a, ?_⟩
  intro s hs
  exact e.injective (hs.trans (e.apply_symm_apply a).symm)

/-- A canonical recipe identifies its own observed output. This says nothing
about an arbitrary supplied object outside that graph (Definition 9.1). -/
theorem canonical_realization_fibre {S C : Type*} {Y : C → Type*}
    (recipe : (c : C) → S → Y c) (c : C) (s : S) :
    ∃! y : Y c, y = recipe c s := by
  exact ⟨recipe c s, rfl, fun _ h => h⟩

/-- The marked placed-family parameter domain in Theorem 9.4. -/
@[ext] structure Placement where
  μ : ℝ
  a : ℝ
  μ_pos : 0 < μ
  a_pos : 0 < a
  a_lt_one : a < 1

def Placement.presentation (P : Placement) : ScalarFunction :=
  fun r => placed P.μ P.a r

theorem placed_presentation_injective : Function.Injective Placement.presentation := by
  intro P Q h
  have he := placed_parameters_unique P.μ_pos P.a_pos Q.μ_pos Q.a_pos
    (fun r hr => congrFun h ⟨r, hr⟩)
  exact Placement.ext he.1 he.2

/-- An exact inverse on the stated placed-family image, not on arbitrary functions. -/
def placementEquivalence : Placement ≃ Set.range Placement.presentation :=
  Equiv.ofInjective Placement.presentation placed_presentation_injective

theorem placement_exact_reconstruction (P : Placement) :
    placementEquivalence.symm (placementEquivalence P) = P :=
  placementEquivalence.symm_apply_apply P

theorem placed_candidate_exact_reconstruction (F : Set.range Placement.presentation) :
    (placementEquivalence (placementEquivalence.symm F)).1 = F.1 := by
  exact congrArg Subtype.val (placementEquivalence.apply_symm_apply F)

/-- A deletion witness remains a witness with every other packet retained. -/
theorem retained_context_deletion {X D T R : Type*}
    (forget : X → D) (target : X → T) (r : R)
    (h : ∃ x y, forget x = forget y ∧ target x ≠ target y) :
    ¬ ∃ decode : R × D → T, ∀ x, decode (r, forget x) = target x := by
  apply deletion_witness_prevents_reconstruction (fun x => (r, forget x)) target
  obtain ⟨x, y, he, hn⟩ := h
  exact ⟨x, y, congrArg (fun d => (r, d)) he, hn⟩

/-- The paper's fixed-offset scale witnesses are both admissible. -/
theorem placement_scale_deletion :
    ∃ P Q : Placement, P.a = Q.a ∧ P.presentation ≠ Q.presentation := by
  let P : Placement := ⟨1, 1/2, by norm_num, by norm_num, by norm_num⟩
  let Q : Placement := ⟨2, 1/2, by norm_num, by norm_num, by norm_num⟩
  refine ⟨P, Q, rfl, ?_⟩
  intro he
  have h := congrArg Placement.μ (placed_presentation_injective he)
  norm_num [P, Q] at h

/-- The paper's fixed-scale offset witnesses are both admissible. -/
theorem placement_offset_deletion :
    ∃ P Q : Placement, P.μ = Q.μ ∧ P.presentation ≠ Q.presentation := by
  let P : Placement := ⟨1, 1/3, by norm_num, by norm_num, by norm_num⟩
  let Q : Placement := ⟨1, 2/3, by norm_num, by norm_num, by norm_num⟩
  refine ⟨P, Q, rfl, ?_⟩
  intro he
  have h := congrArg Placement.a (placed_presentation_injective he)
  norm_num [P, Q] at h

theorem no_placement_decoder_without_scale {R : Type*} (retained : R) :
    ¬ ∃ decode : R × ℝ → ScalarFunction,
      ∀ P : Placement, decode (retained, P.a) = P.presentation :=
  retained_context_deletion Placement.a Placement.presentation retained
    placement_scale_deletion

theorem no_placement_decoder_without_offset {R : Type*} (retained : R) :
    ¬ ∃ decode : R × ℝ → ScalarFunction,
      ∀ P : Placement, decode (retained, P.μ) = P.presentation :=
  retained_context_deletion Placement.μ Placement.presentation retained
    placement_offset_deletion

abbrev Plane := EuclideanSpace ℝ (Fin 2)

theorem plane_quartic_not_orthogonally_additive :
    ¬ OrthogonallyAdditive (fun x : Plane => ‖x‖ ^ 4) := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  exact quartic_not_orthogonal_additive_of_pair (b 0) (b 1)
    (b.orthonormal.1 0) (b.orthonormal.1 1)
    (b.orthonormal.2 (by decide : (0 : Fin 2) ≠ 1))

/-- The same fixed plane admits both composition behaviors, with nonnegative observables. -/
theorem plane_composition_deletion :
    ∃ f g : Plane → ℝ, (∀ x, 0 ≤ f x) ∧ (∀ x, 0 ≤ g x) ∧
      OrthogonallyAdditive f ∧ ¬ OrthogonallyAdditive g := by
  exact ⟨fun x => ‖x‖ ^ 2, fun x => ‖x‖ ^ 4, fun x => by positivity,
    fun x => by positivity, norm_square_orthogonal_additive,
    plane_quartic_not_orthogonally_additive⟩

/-- Even after imposing nonnegative orthogonal additivity, scale remains free. -/
theorem plane_scale_deletion :
    ∃ f g : Plane → ℝ, (∀ x, 0 ≤ f x) ∧ (∀ x, 0 ≤ g x) ∧
      OrthogonallyAdditive f ∧ OrthogonallyAdditive g ∧ f ≠ g := by
  refine ⟨fun x => ‖x‖ ^ 2, fun x => 2 * ‖x‖ ^ 2,
    fun x => by positivity, fun x => by positivity,
    norm_square_orthogonal_additive, ?_, ?_⟩
  · intro x y hxy
    have h := norm_square_orthogonal_additive x y hxy
    dsimp only at h ⊢
    rw [h]
    ring
  · intro he
    let b := EuclideanSpace.basisFun (Fin 2) ℝ
    have h := congrFun he (b 0)
    have hn := b.orthonormal.1 0
    norm_num [hn] at h

theorem no_spatial_observable_decoder {R : Type*} (retained : R) :
    ¬ ∃ decode : R → (Plane → ℝ), ∀ f : Plane → ℝ,
      (∀ x, 0 ≤ f x) → OrthogonallyAdditive f → decode retained = f := by
  rintro ⟨decode, hd⟩
  obtain ⟨f, g, hf, hg, hfa, hga, hne⟩ := plane_scale_deletion
  exact hne ((hd f hf hfa).symm.trans (hd g hg hga))

/-- The packet carries its dimension and the selected function on that very space. -/
structure SpatialPacket where
  dimension : ℕ
  observable : EuclideanSpace ℝ (Fin dimension) → ℝ

theorem spatial_dimension_deletion :
    ∃ P Q : SpatialPacket, P.dimension = 2 ∧ Q.dimension = 3 ∧
      (∀ x, 0 ≤ P.observable x) ∧ (∀ x, 0 ≤ Q.observable x) ∧
      OrthogonallyAdditive P.observable ∧ OrthogonallyAdditive Q.observable := by
  exact ⟨⟨2, fun x => ‖x‖ ^ 2⟩, ⟨3, fun x => ‖x‖ ^ 2⟩, rfl, rfl,
    fun x => by positivity, fun x => by positivity,
    norm_square_orthogonal_additive, norm_square_orthogonal_additive⟩

theorem no_spatial_dimension_decoder {R : Type*} (retained : R) :
    ¬ ∃ decode : R → ℕ, ∀ P : SpatialPacket,
      (∀ x, 0 ≤ P.observable x) → OrthogonallyAdditive P.observable →
      decode retained = P.dimension := by
  rintro ⟨decode, hd⟩
  obtain ⟨P, Q, hP, hQ, hp, hq, hpa, hqa⟩ := spatial_dimension_deletion
  have h := (hd P hp hpa).symm.trans (hd Q hq hqa)
  omega

/-- Corollary 9.5's spatial rigidity conclusion retains the actual dimension
condition and imposes no continuity, measurability, or finite-dimensionality. -/
theorem spatial_observable_reconstruction {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (hdim : (2 : Cardinal) ≤ Module.rank ℝ V) (f : V → ℝ)
    (hf : OrthogonallyAdditive f) (hpos : ∀ x, 0 ≤ f x) :
    ∃! c : ℝ, 0 ≤ c ∧ ∀ x, f x = c * ‖x‖ ^ 2 := by
  obtain ⟨c, hc, he⟩ := nonnegative_orthogonal_quadratic hdim f hf hpos
  obtain ⟨w, hw⟩ := exists_linearIndependent_of_le_rank (n := 2) hdim
  let v : Fin 2 → V := @gramSchmidtNormed ℝ V _ _ _ (Fin 2)
    (inferInstance : LinearOrder (Fin 2))
    (inferInstance : LocallyFiniteOrderBot (Fin 2))
    (inferInstance : WellFoundedLT (Fin 2)) w
  have ho : Orthonormal ℝ v :=
    @gramSchmidt_orthonormal ℝ V _ _ _ (Fin 2)
      (inferInstance : LinearOrder (Fin 2))
      (inferInstance : LocallyFiniteOrderBot (Fin 2))
      (inferInstance : WellFoundedLT (Fin 2)) w hw
  let u := v 0
  have hu : ‖u‖ = 1 := ho.1 0
  refine ⟨c, ⟨hc, he⟩, ?_⟩
  intro d hd
  have h := (hd.2 u).symm.trans (he u)
  simpa only [hu, one_pow, mul_one] using h

/-- The actual differential expression, rather than only its simplified coefficient. -/
theorem spatial_radial_cancellation (D : ℝ) (f : ℝ → ℝ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (x f₂ : ℝ) (hx : 0 < x)
    (hfx : f x ≠ 0) (hf₂ : HasDerivAt (deriv f) f₂ x) :
    (deriv (deriv (fun y => radialWeight ((D - 1) / 2) y * f y)) x /
        (radialWeight ((D - 1) / 2) x * f x) -
      (deriv (deriv f) x / f x + (D - 1) / x * (deriv f x / f x)) = 0) ↔
      D = 1 ∨ D = 3 := by
  rw [radial_residual D f hf x f₂ hx hfx hf₂]
  exact radial_residual_cancellation D x hx

theorem spatial_radial_dimension_three (D : ℝ) (hD : 2 ≤ D) (f : ℝ → ℝ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (x f₂ : ℝ) (hx : 0 < x)
    (hfx : f x ≠ 0) (hf₂ : HasDerivAt (deriv f) f₂ x) :
    (deriv (deriv (fun y => radialWeight ((D - 1) / 2) y * f y)) x /
        (radialWeight ((D - 1) / 2) x * f x) -
      (deriv (deriv f) x / f x + (D - 1) / x * (deriv f x / f x)) = 0) ↔
      D = 3 := by
  rw [radial_residual D f hf x f₂ hx hfx hf₂]
  exact radial_residual_dimension_three D x hD hx

/-- Cancellation at dimension three does not identify the intrinsic profile. -/
theorem radial_cancellation_does_not_identify_profile :
    (∀ x > 0, deriv (deriv (fun y => radialWeight 1 y)) x /
      radialWeight 1 x = 0) ∧
      ¬ (∀ x > 0, (1 : ℝ) = H x) :=
  ⟨constant_profile_radial_residual_three, constant_profile_differs_from_H_on_positive_ray⟩

end
end Sigma.Closure
