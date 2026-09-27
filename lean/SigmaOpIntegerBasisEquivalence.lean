import SigmaOpIntegerEigenbasis
import SigmaOpNonnegativeResolvent
import Mathlib.Topology.Algebra.Module.LinearPMap

namespace Sigma
noncomputable section
open Set Filter
open scoped Topology ComplexConjugate

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem integer_basis_multiplier_domain_dense (b : HilbertBasis ℕ ℂ H) (f : ℕ → ℂ) :
    Dense ((integerBasisMultiplier b f).domain : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply top_unique
  rw [← b.dense_span]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨n, rfl⟩
  exact integer_basis_mem_multiplier_domain b f n

theorem integer_basis_multiplier_adjoint_coordinate [CompleteSpace H]
    (b : HilbertBasis ℕ ℂ H) (f : ℕ → ℝ)
    (y : (integerBasisMultiplier b (fun n => (f n : ℂ))).adjoint.domain) (n : ℕ) :
    b.repr ((integerBasisMultiplier b (fun n => (f n : ℂ))).adjoint y) n =
      (f n : ℂ) * b.repr y.val n := by
  have hi := ((integerBasisMultiplier b (fun n => (f n : ℂ))).adjoint_isFormalAdjoint
    (integer_basis_multiplier_domain_dense b _)).symm
      ⟨b n, integer_basis_mem_multiplier_domain b _ n⟩ y
  rw [integer_basis_multiplier_basis_action, inner_smul_left] at hi
  simpa [b.repr_apply_apply] using hi.symm

theorem integer_basis_real_multiplier_selfAdjoint [CompleteSpace H]
    (b : HilbertBasis ℕ ℂ H) (f : ℕ → ℝ) :
    IsSelfAdjoint (integerBasisMultiplier b (fun n => (f n : ℂ))) := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm
  · refine ⟨?_, ?_⟩
    · intro y hy
      change Memℓp (fun n => (f n : ℂ) * b.repr y n) 2
      have he : (fun n => (f n : ℂ) * b.repr y n) =
          fun n => b.repr ((integerBasisMultiplier b (fun n => (f n : ℂ))).adjoint
            ⟨y, hy⟩) n := funext fun n =>
        (integer_basis_multiplier_adjoint_coordinate b f ⟨y, hy⟩ n).symm
      rw [he]
      exact (b.repr ((integerBasisMultiplier b (fun n => (f n : ℂ))).adjoint
        ⟨y, hy⟩)).property
    · intro x y hxy
      apply b.repr.injective
      apply lp.ext
      funext n
      rw [integer_basis_multiplier_adjoint_coordinate, integer_basis_multiplier_coordinate,
        hxy]
  · exact (integer_basis_multiplier_formal_adjoint b _ (by intro n; simp)).le_adjoint
      (integer_basis_multiplier_domain_dense b _)

theorem integer_basis_multiplier_graph_iff (b : HilbertBasis ℕ ℂ H) (f : ℕ → ℂ)
    (p : H × H) :
    p ∈ (integerBasisMultiplier b f).graph ↔
      ∀ n, b.repr p.2 n = f n * b.repr p.1 n := by
  constructor
  · intro hp
    obtain ⟨x, hx, hy⟩ := (LinearPMap.mem_graph_iff _).mp hp
    rw [← hx, ← hy]
    exact integer_basis_multiplier_coordinate b f x
  · intro hp
    have hd : p.1 ∈ (integerBasisMultiplier b f).domain := by
      change Memℓp (fun n => f n * b.repr p.1 n) 2
      rw [show (fun n => f n * b.repr p.1 n) = fun n => b.repr p.2 n from
        funext fun n => (hp n).symm]
      exact (b.repr p.2).property
    refine (LinearPMap.mem_graph_iff _).mpr ⟨⟨p.1, hd⟩, rfl, ?_⟩
    apply b.repr.injective
    apply lp.ext
    funext n
    rw [integer_basis_multiplier_coordinate, hp n]

theorem integer_basis_multiplier_closed (b : HilbertBasis ℕ ℂ H) (f : ℕ → ℂ) :
    (integerBasisMultiplier b f).IsClosed := by
  have hc (n : ℕ) : Continuous (fun x : H => b.repr x n) :=
    (continuous_apply n).comp (lp.uniformContinuous_coe.continuous.comp b.repr.continuous)
  change IsClosed ((integerBasisMultiplier b f).graph : Set (H × H))
  have he : ((integerBasisMultiplier b f).graph : Set (H × H)) =
      ⋂ n : ℕ, {p | b.repr p.2 n = f n * b.repr p.1 n} := by
    ext p
    simp only [mem_iInter, mem_setOf_eq]
    exact integer_basis_multiplier_graph_iff b f p
  rw [he]
  exact isClosed_iInter fun n => isClosed_eq ((hc n).comp continuous_snd)
    (continuous_const.mul ((hc n).comp continuous_fst))

theorem integer_basis_multiplier_action_hasSum (b : HilbertBasis ℕ ℂ H) (f : ℕ → ℂ)
    (x : (integerBasisMultiplier b f).domain) :
    HasSum (fun n => (f n * b.repr x.val n) • b n) (integerBasisMultiplier b f x) := by
  simpa only [integer_basis_multiplier_coordinate] using
    b.hasSum_repr (integerBasisMultiplier b f x)

theorem integer_basis_graph_le_of_modes (b : HilbertBasis ℕ ℂ H) (f : ℕ → ℂ)
    (G : Submodule ℂ (H × H)) (hG : IsClosed (G : Set (H × H)))
    (hmodes : ∀ n, (b n, f n • b n) ∈ G) :
    (integerBasisMultiplier b f).graph ≤ G := by
  intro p hp
  obtain ⟨x, hx, hy⟩ := (LinearPMap.mem_graph_iff _).mp hp
  change (p.1, p.2) ∈ G
  rw [← hx, ← hy]
  have hsum := (b.hasSum_repr x.val).prod_mk (integer_basis_multiplier_action_hasSum b f x)
  apply hG.mem_of_tendsto hsum
  apply Eventually.of_forall
  intro s
  apply G.sum_mem
  intro n _
  have h := G.smul_mem (b.repr x.val n) (hmodes n)
  convert h using 1
  ext <;> simp [smul_smul, mul_comm]

/-- A genuine compact-test graph approximation of each mode identifies the
closure of any restriction with the entire maximal spectral operator. -/
theorem integer_basis_restriction_closure_eq_of_modes (b : HilbertBasis ℕ ℂ H)
    (f : ℕ → ℂ) (T : H →ₗ.[ℂ] H) (hT : T ≤ integerBasisMultiplier b f)
    (hmodes : ∀ n, (b n, f n • b n) ∈ T.graph.topologicalClosure) :
    T.closure = integerBasisMultiplier b f := by
  have hc : T.IsClosable :=
    (integer_basis_multiplier_closed b f).isClosable.leIsClosable hT
  apply le_antisymm
  · apply LinearPMap.le_of_le_graph
    rw [← hc.graph_closure_eq_closure_graph]
    have h := Submodule.topologicalClosure_mono (LinearPMap.le_graph_of_le hT)
    rwa [(integer_basis_multiplier_closed b f).submodule_topologicalClosure_eq] at h
  · apply LinearPMap.le_of_le_graph
    rw [← hc.graph_closure_eq_closure_graph]
    exact integer_basis_graph_le_of_modes b f _ T.graph.isClosed_topologicalClosure hmodes

theorem integer_basis_real_multiplier_inner (b : HilbertBasis ℕ ℂ H) (f : ℕ → ℝ)
    (x : (integerBasisMultiplier b (fun n => (f n : ℂ))).domain) :
    @inner ℂ H _ x.val (integerBasisMultiplier b (fun n => (f n : ℂ)) x) =
      ((∑' n : ℕ, f n * ‖b.repr x.val n‖^2 : ℝ) : ℂ) := by
  rw [← b.repr.inner_map_map, lp.inner_eq_tsum, Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  rw [integer_basis_multiplier_coordinate]
  simp only [RCLike.inner_apply, Complex.ofReal_mul]
  rw [mul_left_comm, Complex.conj_mul', Complex.ofReal_pow]

theorem integer_basis_real_multiplier_nonnegative (b : HilbertBasis ℕ ℂ H)
    (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    OpNonnegative (integerBasisMultiplier b (fun n => (f n : ℂ))) := by
  intro x
  rw [integer_basis_real_multiplier_inner, Complex.ofReal_re]
  exact tsum_nonneg fun n => mul_nonneg (hf n) (sq_nonneg _)

/-- The unitary matching two complete orthonormal bases. -/
def integerBasisUnitary (b : HilbertBasis ℕ ℂ H) (c : HilbertBasis ℕ ℂ K) :
    H ≃ₗᵢ[ℂ] K := b.repr.trans c.repr.symm

theorem integer_basis_unitary_coordinate (b : HilbertBasis ℕ ℂ H)
    (c : HilbertBasis ℕ ℂ K) (x : H) :
    c.repr (integerBasisUnitary b c x) = b.repr x :=
  c.repr.apply_symm_apply _

theorem integer_basis_unitary_basis (b : HilbertBasis ℕ ℂ H)
    (c : HilbertBasis ℕ ℂ K) (n : ℕ) : integerBasisUnitary b c (b n) = c n := by
  apply c.repr.injective
  rw [integer_basis_unitary_coordinate, b.repr_self, c.repr_self]

/-- The intertwining includes the entire maximal unbounded domain. -/
theorem integer_basis_unitary_domain_iff (b : HilbertBasis ℕ ℂ H)
    (c : HilbertBasis ℕ ℂ K) (f : ℕ → ℂ) (x : H) :
    integerBasisUnitary b c x ∈ (integerBasisMultiplier c f).domain ↔
      x ∈ (integerBasisMultiplier b f).domain := by
  change Memℓp (fun n => f n * c.repr (integerBasisUnitary b c x) n) 2 ↔ _
  rw [integer_basis_unitary_coordinate]
  rfl

theorem integer_basis_unitary_multiplier_action (b : HilbertBasis ℕ ℂ H)
    (c : HilbertBasis ℕ ℂ K) (f : ℕ → ℂ) (x : (integerBasisMultiplier b f).domain) :
    integerBasisUnitary b c (integerBasisMultiplier b f x) =
      integerBasisMultiplier c f ⟨integerBasisUnitary b c x.val,
        (integer_basis_unitary_domain_iff b c f x.val).mpr x.property⟩ := by
  apply c.repr.injective
  apply lp.ext
  funext n
  rw [integer_basis_unitary_coordinate, integer_basis_multiplier_coordinate,
    integer_basis_multiplier_coordinate, integer_basis_unitary_coordinate]

theorem integer_basis_unitary_bounded_multiplier_action (b : HilbertBasis ℕ ℂ H)
    (c : HilbertBasis ℕ ℂ K) (f : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ n, ‖f n‖ ≤ C) (x : H) :
    integerBasisUnitary b c (integerBasisBoundedMultiplier b f C hC hf x) =
      integerBasisBoundedMultiplier c f C hC hf (integerBasisUnitary b c x) := by
  apply c.repr.injective
  apply lp.ext
  funext n
  rw [integer_basis_unitary_coordinate, integer_basis_bounded_multiplier_coordinate,
    integer_basis_bounded_multiplier_coordinate, integer_basis_unitary_coordinate]

end
end Sigma
