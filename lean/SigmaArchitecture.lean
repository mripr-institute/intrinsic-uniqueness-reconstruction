import SigmaCore
import SigmaBregman
import SigmaPlacement

namespace Sigma
noncomputable section
open Filter Set
open scoped Topology

/-- This is the exact three-clause differential component, not the full paper graph. -/
def DifferentialCoreClause (F : ℝ → ℝ) : Prop :=
  ((∀ t > 0, DifferentiableAt ℝ F t) ∧ F 1 = 0 ∧ deriv F 1 = 0 ∧
    ∀ t > 0, HasDerivAt (deriv F) (-(1/t^2)) t) ∨
  ((∀ t > 0, DifferentiableAt ℝ F t) ∧ F 1 = 0 ∧ deriv F 1 = 0 ∧
    ∀ t > 0, HasDerivAt (deriv F) (-(deriv F t+1)^2) t) ∨
  ((∀ t > 0, DifferentiableAt ℝ F t) ∧ HasDerivAt (deriv F) (-1) 1 ∧
    ∀ a > 0, ∀ v > 0, F (a*v)-F a-a*deriv F a*(v-1) = F v)

theorem differential_core_identifies (F : ℝ → ℝ) (h : DifferentialCoreClause F) :
    ∀ t > 0, F t = H t := by
  rcases h with ⟨hd,hv,hs,hc⟩ | ⟨hd,hv,hs,hr⟩ | ⟨hd,h2,hrec⟩
  · exact curvature_reconstruction F hd hc hv hs
  · exact riccati_reconstruction F hd hr hv hs
  · exact recentering_reconstruction F hd hrec h2

theorem differential_core_iff (F : ℝ → ℝ) :
    DifferentialCoreClause F ↔ ∀ t > 0, F t = H t := by
  refine ⟨differential_core_identifies F, ?_⟩
  intro he
  have heN : ∀ t > 0, F =ᶠ[nhds t] H := by
    intro t ht
    filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
    exact he x hx
  have hF : ∀ t > 0, HasDerivAt F (1/t-1) t := by
    intro t ht
    exact (H_hasDerivAt ht).congr_of_eventuallyEq (heN t ht)
  have hF2 : ∀ t > 0, HasDerivAt (deriv F) (-(1/t^2)) t := by
    intro t ht
    apply (reciprocal_hasDerivAt ht).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
    exact (hF x hx).deriv
  apply Or.inl
  refine ⟨fun t ht => (hF t ht).differentiableAt, ?_, ?_, hF2⟩
  · simpa [H, SigmaPresentations.H] using he 1 (by norm_num)
  · simpa using (hF 1 (by norm_num)).deriv

theorem differential_core_pairwise_uniqueness (F G : ℝ → ℝ)
    (hF : DifferentialCoreClause F) (hG : DifferentialCoreClause G) :
    ∀ t > 0, F t = G t := by
  intro t ht
  exact (differential_core_identifies F hF t ht).trans
    (differential_core_identifies G hG t ht).symm

/-- Generic composition of proved inverses; no missing local inverse is manufactured. -/
def presentationEquivalence {S A B : Type*} (eA : S ≃ A) (eB : S ≃ B) : A ≃ B :=
  eA.symm.trans eB

theorem presentationEquivalence_forward {S A B : Type*} (eA : S ≃ A) (eB : S ≃ B) (a : A) :
    presentationEquivalence eA eB a = eB (eA.symm a) := rfl

theorem presentationEquivalence_roundtrip {S A B : Type*} (eA : S ≃ A) (eB : S ≃ B) (a : A) :
    presentationEquivalence eB eA (presentationEquivalence eA eB a) = a := by
  simp [presentationEquivalence]

theorem same_intrinsic_different_contexts {S C : Type*} [Nonempty S] [Nontrivial C] :
    ∃ x y : S × C, x.1 = y.1 ∧ x.2 ≠ y.2 := by
  obtain ⟨s⟩ := ‹Nonempty S›
  obtain ⟨c,d,hcd⟩ := exists_pair_ne C
  exact ⟨(s,c),(s,d),rfl,hcd⟩

/-- Non-identification in the explicitly free product universe. -/
theorem no_context_decoder_from_intrinsic {S C : Type*} [Nonempty S] [Nontrivial C] :
    ¬ ∃ decode : S → C, ∀ x : S × C, decode x.1 = x.2 := by
  rintro ⟨decode,h⟩
  obtain ⟨x,y,hS,hC⟩ := same_intrinsic_different_contexts (S := S) (C := C)
  exact hC ((h x).symm.trans ((congrArg decode hS).trans (h y)))

/-- Deletion witnesses imply failure of reconstruction in their actual candidate universe. -/
theorem deletion_witness_prevents_reconstruction {X D T : Type*}
    (forget : X → D) (target : X → T)
    (h : ∃ x y : X, forget x = forget y ∧ target x ≠ target y) :
    ¬ ∃ reconstruct : D → T, ∀ x, reconstruct (forget x) = target x := by
  rintro ⟨reconstruct,hr⟩
  obtain ⟨x,y,hd,ht⟩ := h
  exact ht ((hr x).symm.trans ((congrArg reconstruct hd).trans (hr y)))

end
end Sigma
