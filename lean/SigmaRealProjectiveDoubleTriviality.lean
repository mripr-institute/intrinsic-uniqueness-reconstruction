import SigmaRealProjectiveKTheory

namespace Sigma
noncomputable section
open Bundle FiniteComplexBundle

private abbrev IncidenceFiber (p : RealProjectivePlane) :=
  (realProjectiveComplexification p).submodule

private theorem projector_rep (p : RealProjectivePlane) (i j : Fin 3) :
    (realProjectiveProjector p i j : ℂ) =
      (p.rep i : ℂ) * (p.rep j : ℂ) / (realVectorSquare p.rep : ℂ) := by
  conv_lhs => rw [← p.mk_rep, real_projective_projector_mk]
  push_cast
  rfl

private theorem square_sum_ne (p : RealProjectivePlane) :
    (realVectorSquare p.rep : ℂ) ≠ 0 := by
  exact_mod_cast (real_vector_square_pos p.rep_nonzero).ne'

private theorem square_sum_formula (p : RealProjectivePlane) :
    (realVectorSquare p.rep : ℂ) =
      (p.rep 0 : ℂ)^2 + (p.rep 1 : ℂ)^2 + (p.rep 2 : ℂ)^2 := by
  simp [realVectorSquare, Fin.sum_univ_succ, add_assoc]

/-- Columns of the actual rank-one orthogonal projector are continuous
sections of the complexified tautological line. -/
private def projectorColumn (p : RealProjectivePlane) (j : Fin 3) : IncidenceFiber p :=
  ⟨fun k => (realProjectiveProjector p k j : ℂ), by
    rw [IncidenceFiber, real_projective_complexification_fiber, Submodule.mem_span_singleton]
    refine ⟨(p.rep j : ℂ) / (realVectorSquare p.rep : ℂ), ?_⟩
    funext k
    change _ * (p.rep k : ℂ) = _
    rw [projector_rep]
    ring⟩

private def doubleForward (u v : Fin 3 → ℂ) : ℂ × ℂ :=
  (u 0 + Complex.I * u 1 + v 2, -u 2 + v 0 - Complex.I * v 1)

private def doubleBackward (p : RealProjectivePlane) (z : ℂ × ℂ) :
    IncidenceFiber p × IncidenceFiber p :=
  (z.1 • projectorColumn p 0 - (Complex.I * z.1) • projectorColumn p 1 -
      z.2 • projectorColumn p 2,
    z.1 • projectorColumn p 2 + z.2 • projectorColumn p 0 +
      (Complex.I * z.2) • projectorColumn p 1)

private theorem double_forward_backward (p : RealProjectivePlane) (z : ℂ × ℂ) :
    doubleForward (doubleBackward p z).1.val (doubleBackward p z).2.val = z := by
  have hn := square_sum_ne p
  have hs := square_sum_formula p
  apply Prod.ext <;>
    simp only [doubleForward, doubleBackward, projectorColumn, Submodule.coe_add,
      Submodule.coe_sub, Submodule.coe_smul, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, projector_rep] <;>
    field_simp <;> rw [hs] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

private theorem double_backward_forward (p : RealProjectivePlane)
    (u v : IncidenceFiber p) : doubleBackward p (doubleForward u.val v.val) = (u, v) := by
  have hu := u.property
  have hv := v.property
  change u.val ∈ (realProjectiveComplexification p).submodule at hu
  change v.val ∈ (realProjectiveComplexification p).submodule at hv
  rw [real_projective_complexification_fiber, Submodule.mem_span_singleton] at hu hv
  obtain ⟨a, ha⟩ := hu
  obtain ⟨b, hb⟩ := hv
  have hau (k : Fin 3) : u.val k = a * (p.rep k : ℂ) := (congrFun ha k).symm
  have hbv (k : Fin 3) : v.val k = b * (p.rep k : ℂ) := (congrFun hb k).symm
  have hn := square_sum_ne p
  have hs := square_sum_formula p
  apply Prod.ext <;> apply Subtype.ext <;> funext k <;>
    simp only [doubleBackward, doubleForward, projectorColumn, Submodule.coe_add,
      Submodule.coe_sub, Submodule.coe_smul, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, projector_rep, hau, hbv] <;>
    field_simp <;> rw [hs] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

/-- The quaternionic two-column matrix trivializes two copies of the actual
complexified line. Its inverse uses only the continuous projective projector. -/
private def doubleFiberEquiv (p : RealProjectivePlane) :
    (IncidenceFiber p × IncidenceFiber p) ≃ₗ[ℂ] (ℂ × ℂ) where
  toFun z := doubleForward z.1.val z.2.val
  invFun := doubleBackward p
  left_inv z := double_backward_forward p z.1 z.2
  right_inv := double_forward_backward p
  map_add' z w := by
    apply Prod.ext <;> simp [doubleForward] <;> ring
  map_smul' a z := by
    apply Prod.ext <;> simp [doubleForward] <;> ring

private abbrev TrivialDouble :=
  (FiniteComplexBundle.trivial (B := RealProjectivePlane) 1).sum
    (FiniteComplexBundle.trivial 1)

private def doubleNativeFiberEquiv (p : RealProjectivePlane) :
    (realProjectiveKLine.sum realProjectiveKLine).Fiber p ≃ₗ[ℂ]
      TrivialDouble.Fiber p :=
  ((realProjectiveComplexFiberEquiv p).prod (realProjectiveComplexFiberEquiv p)).trans
    ((doubleFiberEquiv p).trans
      ((LinearEquiv.funUnique (Fin 1) ℂ ℂ).symm.prod
        (LinearEquiv.funUnique (Fin 1) ℂ ℂ).symm))

private theorem continuous_incidence_coordinate (k : Fin 3) :
    Continuous (fun z : realProjectiveKLine.Total =>
      (realProjectiveComplexFiberEquiv z.proj z.snd).val k) :=
  (continuous_apply k).comp
    (continuous_snd.comp (continuous_subtype_val.comp
      realProjectiveComplexIncidenceHomeomorph.continuous))

private theorem continuous_backward_incidence (first : Bool) :
    Continuous (fun q : RealProjectivePlane × (ℂ × ℂ) =>
      (⟨(q.1, (if first then (doubleBackward q.1 q.2).1 else
        (doubleBackward q.1 q.2).2).val),
        (if first then (doubleBackward q.1 q.2).1 else
          (doubleBackward q.1 q.2).2).property⟩ : RealProjectiveComplexIncidence)) := by
  apply Continuous.subtype_mk
  apply continuous_fst.prod_mk
  apply continuous_pi
  intro k
  have hp (j : Fin 3) : Continuous (fun q : RealProjectivePlane × (ℂ × ℂ) =>
      (realProjectiveProjector q.1 k j : ℂ)) :=
    Complex.continuous_ofReal.comp ((real_projective_projector_continuous k j).comp continuous_fst)
  cases first <;>
    simp only [Bool.false_eq_true, ↓reduceIte, doubleBackward, projectorColumn,
      Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  · exact ((continuous_fst.comp continuous_snd).mul (hp 2)).add
      ((continuous_snd.comp continuous_snd).mul (hp 0)) |>.add
        ((continuous_const.mul (continuous_snd.comp continuous_snd)).mul (hp 1))
  · exact ((continuous_fst.comp continuous_snd).mul (hp 0)).sub
      ((continuous_const.mul (continuous_fst.comp continuous_snd)).mul (hp 1)) |>.sub
        ((continuous_snd.comp continuous_snd).mul (hp 2))

set_option maxHeartbeats 1200000 in
/-- An explicit, continuous, fiberwise complex-linear trivialization of
L ⊕ L. No classification theorem or cohomological calculation is used. -/
def realProjectiveDoubleTrivialization :
    Iso (realProjectiveKLine.sum realProjectiveKLine) TrivialDouble where
  fiber := doubleNativeFiberEquiv
  continuous := by
    apply (continuous_sum_iff _ _ _).mpr
    have hc (first : Bool) (k : Fin 3) :
        Continuous (fun z : (realProjectiveKLine.sum realProjectiveKLine).Total =>
          (realProjectiveComplexFiberEquiv z.proj
            (if first then z.snd.1 else z.snd.2)).val k) := by
      cases first
      · have h := (continuous_incidence_coordinate k).comp
          (continuous_sumSnd realProjectiveKLine realProjectiveKLine)
        exact h
      · have h := (continuous_incidence_coordinate k).comp
          (continuous_sumFst realProjectiveKLine realProjectiveKLine)
        exact h
    have hb := FiberBundle.continuous_proj
      (realProjectiveKLine.sum realProjectiveKLine).Model
      (realProjectiveKLine.sum realProjectiveKLine).Fiber
    have hi : Continuous (fun _ : (realProjectiveKLine.sum realProjectiveKLine).Total => Complex.I) :=
      continuous_const
    constructor
    · have h := (Bundle.Trivial.homeomorphProd RealProjectivePlane (Fin 1 → ℂ)).symm.continuous.comp
        (hb.prod_mk (continuous_pi (fun _ : Fin 1 =>
          ((hc true 0).add (hi.mul (hc true 1))).add (hc false 2))))
      exact h
    · have h := (Bundle.Trivial.homeomorphProd RealProjectivePlane (Fin 1 → ℂ)).symm.continuous.comp
        (hb.prod_mk (continuous_pi (fun _ : Fin 1 =>
          ((hc true 2).neg.add (hc false 0)).sub (hi.mul (hc false 1)))))
      exact h
  continuous_symm := by
    apply (continuous_sum_iff _ _ _).mpr
    have hc : Continuous (fun z : TrivialDouble.Total => (z.proj, (z.snd.1 0, z.snd.2 0))) := by
      have h1 := (Bundle.Trivial.homeomorphProd RealProjectivePlane (Fin 1 → ℂ)).continuous.comp
        (continuous_sumFst (FiniteComplexBundle.trivial 1) (FiniteComplexBundle.trivial 1))
      have h2 := (Bundle.Trivial.homeomorphProd RealProjectivePlane (Fin 1 → ℂ)).continuous.comp
        (continuous_sumSnd (FiniteComplexBundle.trivial 1) (FiniteComplexBundle.trivial 1))
      exact h1.fst.prod_mk (((continuous_apply 0).comp h1.snd).prod_mk
        ((continuous_apply 0).comp h2.snd))
    constructor
    · exact realProjectiveComplexIncidenceHomeomorph.symm.continuous.comp
        ((continuous_backward_incidence true).comp hc)
    · exact realProjectiveComplexIncidenceHomeomorph.symm.continuous.comp
        ((continuous_backward_incidence false).comp hc)

theorem real_projective_k0_double_eq :
    kClass realProjectiveKLine + kClass realProjectiveKLine =
      kClass (FiniteComplexBundle.trivial 1) +
        kClass (FiniteComplexBundle.trivial (B := RealProjectivePlane) 1) := by
  rw [← kClass_sum, ← kClass_sum]
  apply congrArg (fun c : FiniteComplexBundle.Class RealProjectivePlane =>
    AddLocalization.mk c (0 : (⊤ : AddSubmonoid (FiniteComplexBundle.Class RealProjectivePlane))))
  exact Quotient.sound ⟨realProjectiveDoubleTrivialization⟩

end
end Sigma
