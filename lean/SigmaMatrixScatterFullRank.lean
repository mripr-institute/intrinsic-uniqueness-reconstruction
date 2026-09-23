import SigmaMatrixScatterRank
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace Sigma
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix
open scoped Topology

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem absolutely_continuous_ae_outside_proper_subspace
    (μ : Measure (n → ℝ)) (hμ : μ ≪ volume) (S : Submodule ℝ (n → ℝ)) (hS : S ≠ ⊤) :
    ∀ᵐ x ∂μ, x ∉ S := by
  rw [ae_iff]
  simpa only [not_not, Set.setOf_mem_eq] using hμ (addHaar_submodule volume S hS)

omit [DecidableEq n] in
/-- Independent absolutely continuous samples are genuinely in general
linear position up to the dimension; no generic-position premise is used. -/
theorem iid_absolutely_continuous_linearIndependent (μ : Measure (n → ℝ))
    [IsProbabilityMeasure μ] (hμ : μ ≪ volume) (k : ℕ) (hk : k ≤ Fintype.card n) :
    ∀ᵐ Z ∂Measure.pi (fun _ : Fin k => μ), LinearIndependent ℝ Z := by
  induction k with
  | zero => exact Eventually.of_forall (fun _ => linearIndependent_empty_type)
  | succ k ih =>
    have htail := ih (by omega)
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => n → ℝ) 0
    have hp : MeasurePreserving e (Measure.pi (fun _ : Fin (k+1) => μ))
        (μ.prod (Measure.pi (fun _ : Fin k => μ))) :=
      measurePreserving_piFinSuccAbove (fun _ => μ) 0
    have hmeas : MeasurableSet {p : (n → ℝ) × (Fin k → n → ℝ) |
        LinearIndependent ℝ (Fin.cons p.1 p.2)} := by
      apply (isOpen_setOf_linearIndependent (𝕜 := ℝ) (E := n → ℝ)).measurableSet.preimage
      apply Continuous.measurable
      apply continuous_pi
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.cons_zero] using
          (continuous_fst : Continuous (Prod.fst : (n → ℝ) × (Fin k → n → ℝ) → n → ℝ))
      · simpa only [Fin.cons_succ] using (continuous_apply j).comp
          (continuous_snd : Continuous (Prod.snd : (n → ℝ) × (Fin k → n → ℝ) → Fin k → n → ℝ))
    have hprod : ∀ᵐ p ∂μ.prod (Measure.pi (fun _ : Fin k => μ)),
        LinearIndependent ℝ (Fin.cons p.1 p.2) := by
      apply (ae_prod_iff_ae_ae hmeas).mpr
      apply (ae_ae_comm hmeas).mpr
      filter_upwards [htail] with Z hZ
      have hproper : Submodule.span ℝ (range Z) ≠ ⊤ := by
        intro he
        have hd := finrank_span_eq_card hZ
        rw [he, finrank_top] at hd
        simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hd
        omega
      filter_upwards [absolutely_continuous_ae_outside_proper_subspace μ hμ _ hproper] with x hx
      exact linearIndependent_fin_cons.mpr ⟨hZ,hx⟩
    have h := hp.quasiMeasurePreserving.ae hprod
    simpa [e, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_zero, Fin.consEquiv] using h

omit [DecidableEq n] in
theorem iid_absolutely_continuous_spans (μ : Measure (n → ℝ))
    [IsProbabilityMeasure μ] (hμ : μ ≪ volume) (m : ℕ) (hm : Fintype.card n ≤ m) :
    ∀ᵐ Z ∂Measure.pi (fun _ : Fin m => μ), Submodule.span ℝ (range Z) = ⊤ := by
  induction m, hm using Nat.le_induction with
  | base =>
    filter_upwards [iid_absolutely_continuous_linearIndependent μ hμ (Fintype.card n) le_rfl] with Z hZ
    exact hZ.span_eq_top_of_card_eq_finrank' (by simp)
  | succ m hm ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => n → ℝ) 0
    have hp : MeasurePreserving e (Measure.pi (fun _ : Fin (m+1) => μ))
        (μ.prod (Measure.pi (fun _ : Fin m => μ))) :=
      measurePreserving_piFinSuccAbove (fun _ => μ) 0
    have hprod : ∀ᵐ p ∂μ.prod (Measure.pi (fun _ : Fin m => μ)),
        Submodule.span ℝ (range p.2) = ⊤ := quasiMeasurePreserving_snd.ae ih
    have htail := hp.quasiMeasurePreserving.ae hprod
    filter_upwards [htail] with Z hZ
    change Submodule.span ℝ (range (Fin.tail Z)) = ⊤ at hZ
    apply top_unique
    rw [← hZ]
    apply Submodule.span_mono
    rintro v ⟨j,rfl⟩
    exact ⟨j.succ,rfl⟩

omit [DecidableEq n] in
theorem matrix_posDef_of_posSemidef_full_rank (M : Matrix n n ℝ) (hM : M.PosSemidef)
    (hr : M.rank = Fintype.card n) : M.PosDef := by
  have hk : LinearMap.ker M.mulVecLin = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    change M.rank+Module.finrank ℝ (LinearMap.ker M.mulVecLin) = Module.finrank ℝ (n → ℝ) at h
    rw [hr, Module.finrank_fintype_fun_eq_card] at h
    omega
  refine ⟨hM.1, fun x hx => ?_⟩
  apply lt_of_le_of_ne (hM.2 x)
  intro he
  have hz : x ∈ LinearMap.ker M.mulVecLin :=
    (hM.dotProduct_mulVec_zero_iff x).mp he.symm
  exact hx (by simpa only [hk, Submodule.mem_bot] using hz)

omit [DecidableEq n] in
theorem matrix_sample_scatter_posDef_of_span_top {m : ℕ} (Z : Fin m → n → ℝ)
    (hZ : Submodule.span ℝ (range Z) = ⊤) : (matrixSampleScatter Z).PosDef := by
  apply matrix_posDef_of_posSemidef_full_rank _ (matrix_sample_scatter_posSemidef Z)
  rw [matrix_sample_scatter_rank, hZ, finrank_top, Module.finrank_fintype_fun_eq_card]

theorem matrix_gaussian_sample_scatter_ae_posDef {m : ℕ} (hm : Fintype.card n ≤ m)
    (X : Matrix n n ℝ) (hX : X.PosDef) :
    ∀ᵐ Z ∂matrixGaussianSampleMeasure m X hX, (matrixSampleScatter Z).PosDef := by
  have hμ : matrixGaussianMeasure X hX ≪ volume := by
    rw [matrix_gaussian_measure_density X hX]
    exact withDensity_absolutelyContinuous _ _
  filter_upwards [iid_absolutely_continuous_spans (matrixGaussianMeasure X hX) hμ m hm] with Z hZ
  exact matrix_sample_scatter_posDef_of_span_top Z hZ

theorem matrix_gaussian_sample_scatter_ae_posDef_iff (m : ℕ)
    (X : Matrix n n ℝ) (hX : X.PosDef) :
    (∀ᵐ Z ∂matrixGaussianSampleMeasure m X hX, (matrixSampleScatter Z).PosDef) ↔
      Fintype.card n ≤ m := by
  constructor
  · intro h
    by_contra hm
    obtain ⟨Z,hZ⟩ := h.exists
    exact matrix_sample_scatter_not_posDef_of_small_sample (Nat.lt_of_not_ge hm) Z hZ
  · intro hm
    exact matrix_gaussian_sample_scatter_ae_posDef hm X hX

theorem matrix_real_posDef_iff_posSemidef_det_ne_zero (M : Matrix n n ℝ) :
    M.PosDef ↔ M.PosSemidef ∧ M.det ≠ 0 := by
  constructor
  · intro h
    exact ⟨h.posSemidef,h.det_pos.ne'⟩
  · rintro ⟨hs,hd⟩
    apply matrix_posDef_of_posSemidef_full_rank M hs
    exact Matrix.rank_of_isUnit M ((Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hd))

omit [DecidableEq n] in
theorem matrix_real_posSemidef_isClosed : IsClosed {M : Matrix n n ℝ | M.PosSemidef} := by
  have he : {M : Matrix n n ℝ | M.PosSemidef} =
      {M | Mᴴ = M} ∩ ⋂ x : n → ℝ, {M | 0 ≤ dotProduct (star x) (M *ᵥ x)} := by
    ext M
    simp only [mem_setOf_eq, mem_inter_iff, mem_iInter]
    rfl
  rw [he]
  apply (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).inter
  apply isClosed_iInter
  intro x
  apply isClosed_le continuous_const
  simp only [Matrix.mulVec, dotProduct]
  fun_prop

theorem matrix_real_posDef_measurableSet : MeasurableSet {M : Matrix n n ℝ | M.PosDef} := by
  have he : {M : Matrix n n ℝ | M.PosDef} =
      {M | M.PosSemidef} ∩ {M | M.det ≠ 0} := by
    ext M
    exact matrix_real_posDef_iff_posSemidef_det_ne_zero M
  rw [he]
  exact matrix_real_posSemidef_isClosed.measurableSet.inter
    (isClosed_eq continuous_id.matrix_det continuous_const).measurableSet.compl

/-- The same exact threshold holds for the actual scatter pushforward law. -/
theorem matrix_wishart_ae_posDef_iff (m : ℕ) (X : Matrix n n ℝ) (hX : X.PosDef) :
    (∀ᵐ W ∂matrixWishartMeasure m X hX, W.PosDef) ↔ Fintype.card n ≤ m := by
  rw [matrixWishartMeasure, ae_map_iff
    (matrix_sample_scatter_continuous m).measurable.aemeasurable matrix_real_posDef_measurableSet]
  exact matrix_gaussian_sample_scatter_ae_posDef_iff m X hX

end
end Sigma
