import SigmaOpSesquilinearForm

namespace Sigma
noncomputable section
open Set Filter
open scoped Topology ContDiff

/-- Finite spectral projections are in the actual generator domain. -/
def laguerreFiniteDomainProjection (x : LaguerreWeightedHilbert) (s : Finset ℕ) :
    (laguerreSpectralOperator id).domain :=
  ∑ n ∈ s, laguerreCoefficient x n •
    ⟨laguerreHilbertBasis n, laguerre_basis_mem_spectral_domain id n⟩

theorem laguerre_finite_domain_projection_coefficient
    (x : LaguerreWeightedHilbert) (s : Finset ℕ) (n : ℕ) :
    laguerreCoefficient (laguerreFiniteDomainProjection x s).val n =
      if n ∈ s then laguerreCoefficient x n else 0 := by
  classical
  simp [laguerreFiniteDomainProjection, laguerreCoefficient, map_sum,
    map_smul, HilbertBasis.repr_self, lp.single_apply, Finset.sum_ite_eq', eq_comm]

theorem laguerre_finite_domain_projection_energy
    (x : LaguerreWeightedHilbert) (s : Finset ℕ) :
    ‖laguerreSpectralOperator Real.sqrt
      ⟨(laguerreFiniteDomainProjection x s).val,
        laguerre_integer_domain_le_square_root (laguerreFiniteDomainProjection x s).property⟩‖^2 =
      ∑ n ∈ s, (n : ℝ) * ‖laguerreCoefficient x n‖^2 := by
  rw [laguerre_square_root_energy]
  simp_rw [laguerre_finite_domain_projection_coefficient]
  rw [tsum_eq_sum (s := s)]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [if_pos hn]
  · intro n hn
    simp [hn]

theorem laguerre_finite_domain_projection_pairing
    (x : LaguerreWeightedHilbert) (s : Finset ℕ) :
    @inner ℂ LaguerreWeightedHilbert _ x
      (laguerreSpectralOperator id (laguerreFiniteDomainProjection x s)) =
      ((∑ n ∈ s, (n : ℝ) * ‖laguerreCoefficient x n‖^2 : ℝ) : ℂ) := by
  classical
  have ha : laguerreSpectralOperator id (laguerreFiniteDomainProjection x s) =
      ∑ n ∈ s, laguerreCoefficient x n • ((n : ℂ) • laguerreHilbertBasis n) := by
    change (laguerreSpectralOperator id).toFun (∑ n ∈ s, _) = _
    simp only [map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro n _
    exact congrArg (fun z => laguerreCoefficient x n • z)
      (laguerre_spectral_basis_action id n)
  rw [ha, inner_sum, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [inner_smul_right, inner_smul_right,
    ← inner_conj_symm (𝕜 := ℂ) x (laguerreHilbertBasis n),
    ← HilbertBasis.repr_apply_apply]
  change laguerreCoefficient x n * ((n : ℂ) * starRingEnd ℂ (laguerreCoefficient x n)) = _
  rw [mul_left_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

/-- A bound on the differential energy pairing forces membership in the
full square-root domain. This uses finite spectral projections and proves
actual summability; it imposes no boundary traces. -/
theorem laguerre_square_root_mem_of_energy_bound
    (x : LaguerreWeightedHilbert) (C : ℝ)
    (hbound : ∀ v : (laguerreSpectralOperator id).domain,
      ‖@inner ℂ LaguerreWeightedHilbert _ x (laguerreSpectralOperator id v)‖ ≤
        C * ‖laguerreSpectralOperator Real.sqrt
          ⟨v.val, laguerre_integer_domain_le_square_root v.property⟩‖) :
    x ∈ (laguerreSpectralOperator Real.sqrt).domain := by
  rw [laguerre_square_root_domain_iff]
  apply summable_of_sum_le (c := C^2) (fun n => by positivity)
  intro s
  have hb := hbound (laguerreFiniteDomainProjection x s)
  rw [laguerre_finite_domain_projection_pairing, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun n _ => by positivity)] at hb
  have he := laguerre_finite_domain_projection_energy x s
  have hn := norm_nonneg (laguerreSpectralOperator Real.sqrt
    ⟨(laguerreFiniteDomainProjection x s).val,
      laguerre_integer_domain_le_square_root (laguerreFiniteDomainProjection x s).property⟩)
  nlinarith [sq_nonneg (C - ‖laguerreSpectralOperator Real.sqrt
    ⟨(laguerreFiniteDomainProjection x s).val,
      laguerre_integer_domain_le_square_root (laguerreFiniteDomainProjection x s).property⟩‖)]

/-- The energy bound need only be checked on the literal compact-interior
smooth differential domain. Graph-core approximation supplies all other tests. -/
theorem laguerre_square_root_mem_of_compact_energy_bound
    (x : LaguerreWeightedHilbert) (C : ℝ)
    (hbound : ∀ u : laguerreMinimalOperator.domain,
      ‖@inner ℂ LaguerreWeightedHilbert _ x (laguerreMinimalOperator u)‖ ≤
        C * ‖laguerreSpectralOperator Real.sqrt
          ⟨u.val, laguerre_integer_domain_le_square_root
            (laguerre_minimal_le_spectral.1 u.property)⟩‖) :
    x ∈ (laguerreSpectralOperator Real.sqrt).domain := by
  apply laguerre_square_root_mem_of_energy_bound x C
  intro v
  have hmem : (v.val, laguerreSpectralOperator id v) ∈
      laguerreMinimalOperator.graph.topologicalClosure := by
    rw [laguerre_minimal_closable.graph_closure_eq_closure_graph]
    change (v.val, laguerreSpectralOperator id v) ∈ laguerreCanonicalOperator.graph
    rw [laguerre_canonical_eq_spectral]
    exact LinearPMap.mem_graph _ v
  obtain ⟨p,hp,ht⟩ := mem_closure_iff_seq_limit.mp hmem
  choose u hu1 hu2 using fun k => (LinearPMap.mem_graph_iff _).mp (hp k)
  let w : ℕ → (laguerreSpectralOperator id).domain := fun k =>
    ⟨(u k).val, laguerre_minimal_le_spectral.1 (u k).property⟩
  have hv : Tendsto (fun k => (w k).val) atTop (𝓝 v.val) := by
    exact ((continuous_fst.tendsto _).comp ht).congr'
      (Eventually.of_forall fun k => (hu1 k).symm)
  have hAv : Tendsto (fun k => laguerreSpectralOperator id (w k)) atTop
      (𝓝 (laguerreSpectralOperator id v)) := by
    apply ((continuous_snd.tendsto _).comp ht).congr'
    exact Eventually.of_forall fun k => (hu2 k).symm.trans (laguerre_minimal_le_spectral.2 rfl)
  have hroot := laguerre_square_root_tendsto_of_graph w v hv hAv
  apply le_of_tendsto_of_tendsto
    ((tendsto_const_nhds.inner (𝕜 := ℂ) hAv).norm) (hroot.norm.const_mul C)
  apply Eventually.of_forall
  intro k
  have hb := hbound (u k)
  have ha : laguerreMinimalOperator (u k) = laguerreSpectralOperator id (w k) :=
    laguerre_minimal_le_spectral.2 rfl
  simpa only [ha] using hb

/-- A genuine weighted weak derivative in L2 suffices for membership in the
square-root domain. The hypothesis is a differential test identity, not a
spectral-domain assumption or an endpoint trace. -/
theorem laguerre_square_root_mem_of_compact_gradient_pairing
    (x g : LaguerreWeightedHilbert)
    (hpair : ∀ (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f),
      tsupport f ⊆ Ioi 0 →
      @inner ℂ LaguerreWeightedHilbert _ x (smoothCompactL2Image f hf hs) =
        @inner ℂ LaguerreWeightedHilbert _ g (smoothCompactGradient f hf hs)) :
    x ∈ (laguerreSpectralOperator Real.sqrt).domain := by
  apply laguerre_square_root_mem_of_compact_energy_bound x ‖g‖
  intro u
  have humem : u.val ∈ laguerreCompactTestDomain := by
    rw [← laguerre_minimal_domain]
    exact u.property
  obtain ⟨f,hf,hs,hpos,huf⟩ := humem
  have he := smooth_compact_vector_eq_of_ae u.val f hf hs huf
  have hu : u = ⟨smoothCompactL2Vector f hf hs, laguerre_compact_test_mem f hf hs hpos⟩ :=
    Subtype.ext he.symm
  rw [hu, laguerre_minimal_test_action f hf hs hpos, hpair f hf hs hpos]
  have hb := norm_inner_le_norm (𝕜 := ℂ) g (smoothCompactGradient f hf hs)
  rwa [smooth_compact_gradient_norm_eq_root] at hb

theorem laguerre_square_root_generator_pairing
    (x : (laguerreSpectralOperator Real.sqrt).domain)
    (y : (laguerreSpectralOperator id).domain) :
    @inner ℂ LaguerreWeightedHilbert _ x.val (laguerreSpectralOperator id y) =
      @inner ℂ LaguerreWeightedHilbert _ (laguerreSpectralOperator Real.sqrt x)
        (laguerreSpectralOperator Real.sqrt
          ⟨y.val, laguerre_integer_domain_le_square_root y.property⟩) := by
  let yr : (laguerreSpectralOperator Real.sqrt).domain :=
    ⟨y.val, laguerre_integer_domain_le_square_root y.property⟩
  have hy : laguerreSpectralOperator Real.sqrt yr ∈ (laguerreSpectralOperator Real.sqrt).domain :=
    (laguerre_square_root_image_domain_iff yr).mpr y.property
  have h := laguerre_spectral_formal_adjoint Real.sqrt x
    ⟨laguerreSpectralOperator Real.sqrt yr,hy⟩
  rw [laguerre_square_root_squared y] at h
  exact h.symm

theorem smooth_compact_image_gradient_pairing (f u : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u)
    (hs : HasCompactSupport f) (hus : HasCompactSupport u) :
    @inner ℂ LaguerreWeightedHilbert _ (smoothCompactL2Vector f hf hs)
      (smoothCompactL2Image u hu hus) =
      @inner ℂ LaguerreWeightedHilbert _ (smoothCompactGradient f hf hs)
        (smoothCompactGradient u hu hus) := by
  rw [smooth_compact_gradient_inner]
  have h := laguerre_square_root_generator_pairing
    ⟨smoothCompactL2Vector f hf hs,
      laguerre_integer_domain_le_square_root (smooth_compact_mem_laguerre_domain f hf hs)⟩
    ⟨smoothCompactL2Vector u hu hus, smooth_compact_mem_laguerre_domain u hu hus⟩
  rwa [laguerre_spectral_extends_differential_test] at h

/-- Exact weak-gradient characterization of the square-root domain. The
separate remaining AC bridge must establish this test identity from the
classical derivative of every finite-energy locally AC representative. -/
theorem laguerre_square_root_domain_iff_weak_gradient (x : LaguerreWeightedHilbert) :
    x ∈ (laguerreSpectralOperator Real.sqrt).domain ↔
      ∃ g : LaguerreWeightedHilbert,
        ∀ (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f),
          tsupport f ⊆ Ioi 0 →
          @inner ℂ LaguerreWeightedHilbert _ x (smoothCompactL2Image f hf hs) =
            @inner ℂ LaguerreWeightedHilbert _ g (smoothCompactGradient f hf hs) := by
  constructor
  · intro hx
    obtain ⟨u,hu,hus,_,g,hv,hg,_⟩ := laguerre_weighted_gradient_completion ⟨x,hx⟩
    refine ⟨g, fun f hf hs _ => ?_⟩
    apply tendsto_nhds_unique (hv.inner (𝕜 := ℂ) tendsto_const_nhds)
    convert hg.inner (𝕜 := ℂ) (tendsto_const_nhds
      (x := smoothCompactGradient f hf hs)) using 1
    funext k
    exact smooth_compact_image_gradient_pairing (u k) f (hu k) hf (hus k) hs
  · rintro ⟨g,hg⟩
    exact laguerre_square_root_mem_of_compact_gradient_pairing x g hg

end
end Sigma
